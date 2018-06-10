classdef SphericalTriangle < handle % < SphericalPolygon?
%SphericalTriangle
%
% FIXME



% Please report bugs and inquiries to:
%
% Name    : Rody P.S. Oldenhuis
% E-mail  : oldenhuis@gmail.com
% Licence : 2-clause BSD (see License.txt)


% If you find this work useful, please consider a donation:
% https://www.paypal.me/RodyO/3.5


% Change log
%{
2018/June:
- Removed affiliation info & updated license

2014/February/14 (Rody Oldenhuis)
- Completed documentation

2011/July (Rody Oldenhuis)
- collected all the separate functions into this value class
%}

    %% Properties

    properties (Access = public)
        A1, A2  % tip angles
        B1, B2  % 1 == "inner", 2 == "outer"
        C1, C2

        a1, a2  % anglular lengths of the sides
        b1, b2  % 1 == "small arc", 2 == "large arc"
        c1, c2

        sphereRadius = 1  % Needed for distance functions etc.
    end

    properties (Dependent, Access = public)
        sides
        perimeter
        area
    end

    properties (Hidden, Access = private)
        originalSize
        unit = 'deg'
    end

    %% Public methods

    methods

        %% Constructor

        function obj = SphericalTriangle(varargin)

            % Allow empty triangles
            if nargin == 0
                return; end

            angles = varargin{1};
            sz = size(angles);
            if ~any(sz==6)
                error(...
                'SphericalTriangle:invalid_argument_dimension', ...
                'The angles array must have at least one dimension equal to 6.');
            end

            % Parse parameter/value pairs
            if nargin > 1

               obj.parsePvPairs(varargin(2:end));

            end


            % Split input and assign to correct properties
            dim = find(sz==6,1,'first');

            obj.originalSize = sz;
            obj.originalSize(dim) = 1;

            inds = repmat({':'}, 1,ndims(angles));
            angles

            inds(dim) = 1;  obj.a1 = angles(inds{:});  obj.a1 = obj.a1(:);
            inds(dim) = 2;  obj.b1 = angles(inds{:});  obj.b1 = obj.b1(:);
            inds(dim) = 3;  obj.c1 = angles(inds{:});  obj.c1 = obj.c1(:);
            inds(dim) = 4;  obj.A1 = angles(inds{:});  obj.A1 = obj.A1(:);
            inds(dim) = 5;  obj.B1 = angles(inds{:});  obj.B1 = obj.B1(:);
            inds(dim) = 6;  obj.C1 = angles(inds{:});  obj.C1 = obj.C1(:);

            obj.a2 = NaN(size(obj.a1));   obj.A2 = NaN(size(obj.a1));
            obj.b2 = NaN(size(obj.a1));   obj.B2 = NaN(size(obj.a1));
            obj.c2 = NaN(size(obj.a1));   obj.C2 = NaN(size(obj.a1));

            % Figure out which angles are missing, and which are given
            % Convention: [ a,b,c, A,B,C ]
            for ii = 1:size(obj.a1,1)

                triangle = [...
                    obj.a1(ii) obj.b1(ii) obj.c1(ii),...
                    obj.A1(ii) obj.B1(ii) obj.C1(ii)];

                nans = sum(isnan(triangle));
                if nans > 3
                    warning(...
                        'SphericalTriangle:underdetermined_triangle',...
                        'Insufficient information to construct triangle no. %d; inserting NaN.',ii);
                end
                if nans < 3
                    % TODO: check values

                    warning(...
                        'SphericalTriangle:overdetermined_triangle',...
                        'Triangle no. %d is overconstrained, and values are inconsistent; inserting NaN.',ii);
                end

%                     obj.a1(ii) obj.b1(ii) obj.c1(ii),...
%                     obj.A1(ii) obj.B1(ii) obj.C1(ii)];
%
%
%                 [a1, b1, c1, a2, b2, c2] = aaa(A, B, C)
%                 [b1, c1, C1, b2, c2, C2] = aas(A, B, a)
%                 [C1, a1, b1, C2, a2, b2] = asa(A, B, c)
%                 [c1, A1, B1, c2, A2, B2] = sas(a, C, b)
%                 [B1, C1, c1, B2, C2, c2] = ssa(a, b, A)
%                 [A1, B1, C1, A2, B2, C2] = sss(a, b, c)

            end

        end % constructor

        %% Geometry

        % Return all distances in an array
        function D = get.sides(obj)
            D = obj.sphereRadius * (pi/180)^(strcmp(obj.unit,'deg')) * [
                obj.a1(:), obj.b1(:), obj.c1(:),...
                obj.a2(:), obj.b2(:), obj.c2(:)];
        end

        function S = sphericalExcess(obj)
            S = [
                obj.A1(:) + obj.B1(:) + obj.C1(:),...
                obj.A2(:) + obj.B2(:) + obj.C2(:)] - pi;
        end

        function D = sphericalDefect(obj)
            S = obj.sides;
            % BUG: radians/degrees is not general
            % BUG: multiplication with radius (in obj.sides) is wrong
            D = 2*pi - [sum(S(:,1:3),2) sum(S(:,4:6),2)];
        end

        % Perimiter
        function P = get.perimeter(obj)
            S = obj.sides;
            % BUG: radians/degrees is not general
            % BUG: multiplication with radius (in obj.sides) is wrong
            P = [sum(S(:,1:3),2) sum(S(:,4:6),2)];
        end

        % Areas of all triangles
        function A = get.area(obj)
            A = obj.sphereRadius^2 * ( (pi/180)^(strcmp(obj.unit,'deg')) * [
                obj.A1(:) + obj.B1(:) + obj.C1(:),...
                obj.A2(:) + obj.B2(:) + obj.C2(:)] - pi );
        end


        function yn = containsPoint(obj, P)
        end

        %% Overloaded methods

        function ie = isempty(obj)
            ie = ...
                isempty(obj.A1) && ...
                isequal(...
                    obj.A1,obj.A2, obj.B1,obj.B2, obj.C1,obj.C2,...
                    obj.a1,obj.a2, obj.b1,obj.b2, obj.c1,obj.c2);
        end

    end % public methods block

    % methods for internal use
    methods (Hidden, Access = private)

        % Parse parameter/value pairs on object construction
        function parsePvPairs(obj, pvPairs)

            parameters = pvPairs(1:2:end);
            values     = pvPairs(2:2:end);

            for ii = 1:numel(parameters)

                parameter = parameters{ii};
                value     = values{ii};

                switch lower(parameter)

                    case {'r' 'radius' 'sphereradius'}
                        if ~isnumeric(value) || ~isscalar(value)
                            warning(...
                                'SphericalTriangle:invalid_radius',...
                                'Sphere radius must be a scalar.');
                            continue;
                        end
                        obj.sphereRadius = value;

                    case {'unit' 'units'}
                        if ~ischar(value)
                            warning(...
                                'SphericalTriangle:invalid_unit',...
                                'Units must be specified via ''char'' argument; got ''%s''.', class(value));
                            continue
                        end
                        switch lower(value)
                            case {'d' 'deg' 'degree' 'degrees'}
                                obj.unit = 'deg';
                            case {'r' 'rad' 'radian' 'radians'}
                                obj.unit = 'rad';
                            otherwise
                                warning(...
                                    'SphericalTriangle:unsupported_unit',...
                                    'Unsupported unit: ''%s''. Supported units are ''degrees'' and ''radians''.', value);
                                continue;
                        end

                    otherwise
                        warning(...
                            'SphericalTriangle:invalid_parameter',...
                            'Invalid option: ''%s''. Ignoring...', parameter);
                        continue
                end
            end
        end

        %
        function triangleFromThreeAngles(obj, a,b,c, A,B,C)
        end

        %
        function triangleFromThreePoints(obj, x, y, z)

            if strcmp(obj.unit, 'deg')
                x = pi*x/180;
                y = pi*y/180;
                z = pi*z/180;
            end

        end

    end

    % These methods are also accessible without class instance
    methods (Static, Access = public)

        %% angle-angle-angle

        % radians
        function [a1, b1, c1, a2, b2, c2] = aaa(A, B, C)
        %AAA  compute both solutions to the angle-angle-angle problem, in radians.
        %
        %   AAA(A, B, C) will result in NaNs if the existence condition
        %   |pi - |A|-|B|| <= |C| <= pi - ||A| - |B||
        %   is not met.
        %
        %   See also SphericalTriangle.aaad.

            % first solution
            a1 = SphericalTriangle.acos2((cos(A) + cos(B).*cos(C)) ./ (sin(B).*sin(C)), A);
            b1 = SphericalTriangle.acos2((cos(B) + cos(A).*cos(C)) ./ (sin(A).*sin(C)), B);
            c1 = SphericalTriangle.acos2((cos(C) + cos(A).*cos(B)) ./ (sin(A).*sin(B)), C);

            % second solution
            a2 = 2*pi - a;
            b2 = 2*pi - b;
            c2 = 2*pi - c;

            % check constraints
            indices = ( abs(pi - abs(A)-abs(B)) <= abs(C) <= pi - abs(abs(A)-abs(B)) );
            a1(indices) = NaN;    a2(indices) = NaN;
            b1(indices) = NaN;    b2(indices) = NaN;
            c1(indices) = NaN;    c2(indices) = NaN;

        end

        % degrees
        function [a1, b1, c1, a2, b2, c2] = aaad(A, B, C)
        %AAAD  gives both solutions to the angle-angle-angle problem, in degrees.
        %
        %   AAAD(A, B, C) will result in NaNs if the existence condition
        %   |pi - |A|-|B|| <= |C| <= pi - ||A| - |B||
        %   is not met.
        %
        %   See also SphericalTriangle.aaa.

            % find both solutions by calling aaa directly
            r2d = 180/pi;   d2r = 1/r2d;
            [A, B, C] = deal(A*d2r, B*d2r, C*d2r);
            [a1, b1, c1, a2, b2, c2] = SphericalTriangle.aaa(A, B, C);
            [a1, b1, c1, a2, b2, c2] = deal(a1*r2d, b1*r2d, c1*r2d, a2*r2d, b2*r2d, c2*r2d);

        end

        %% angle-angle-side

        % radians
        function [b1, c1, C1, b2, c2, C2] = aas(A, B, a)
        %AAS   gives both solutions to the angle-angle-side problem, in radians.
        %
        %   AAS(A, B, a) may result in a vector filled with NaNs if the existence
        %   condition |sin(B)sin(a)| <= |sin(A)| is not met. This function uses the
        %   Middle Side Law function MSL.m and Middle Angle Law function MAL.m to
        %   determine the solutions.
        %
        %   See also sphricaltrig.aasd.

            % first solution
            b1 = mod( asin( (sin(B).*sin(a))./sin(A) ), 2*pi);
            c1 = SphericalTriangle.msl(a, b1, A, B);
            C1 = SphericalTriangle.mal(A, B, a, b1);

            % second solution
            b2 = mod((pi - b1), 2*pi);
            c2 = SphericalTriangle.msl(a, b2, A, B);
            C2 = SphericalTriangle.mal(A, B, a, b2);

            % check constraints
            indices = (abs(sin(B).*sin(a)) > abs(sin(A)));
            b1(indices) = NaN;    c1(indices) = NaN;
            C1(indices) = NaN;    b2(indices) = NaN;
            c2(indices) = NaN;    C2(indices) = NaN;

        end

        % degrees
        function [b1, c1, C1, b2, c2, C2] = aasd(A, B, a)
        %AASD   gives both solutions to the angle-angle-side problem, in degrees.
        %
        %   AASD(A, B, a) may result in a vector fliled with NaNs if the existence
        %   condition |sin(B)sin(a)| <= |sin(A)| is not met. This function uses the
        %   Middle Side Law function MSL.m and Middle Angle Law function MAL.m to
        %   determine the solutions.
        %
        %   See also sphricaltrig.aas.

            % find both solutions by calling aas directly
            r2d = 180/pi;   d2r = 1/r2d;
            [A, B, a] = deal(A*d2r, B*d2r, a*d2r);
            [b1, c1, C1, b2, c2, C2] = SphericalTriangle.aas(A, B, a);
            [b1, c1, C1, b2, c2, C2] = deal(b1*r2d, c1*r2d, C1*r2d, b2*r2d, c2*r2d, C2*r2d);

        end

        %% angle-side-angle

        % radians
        function [C1, a1, b1, C2, a2, b2] = asa(A, B, c)
        %ASA   gives both solutions to the angle-side-angle problem, in radians.
        %
        %   ASA(A, B, c) returns the missing values C, a, b. It uses the
        %   four-quadrant arccosine function ACOS2 to determine these values.
        %
        %   See also sphricaltrig.asad.

            % first solution
            % NOTE: normal acos (in stead of acos2) is indeed correct.
            C1 = acos( -cos(A).*cos(B) + sin(A).*sin(B).*cos(c));
            a1 = acos( (cos(A) + cos(B).*cos(C1))./(sin(B).*sin(C1)));
            b1 = acos( (cos(B) + cos(A).*cos(C1))./(sin(A).*sin(C1)));

            % second solution
            C2 = 2*pi - C1;
            a2 = mod((a1 + pi), 2*pi);
            b2 = mod((b1 + pi), 2*pi);

        end

        % degrees
        function [C1, a1, b1, C2, a2, b2] = asad(A, B, c)
        %ASAD   gives both solutions to the angle-side-angle problem, in degrees.
        %
        %   ASAD(A, B, c) returns the missing values C, a, b. It uses the
        %   four-quadrant arccosine function ACOS2D to determine these values.
        %
        %   See also sphricaltrig.asa

            % Rody P.S. Oldenhuis
            % Delft University of Technology
            % Last edited: 23/Feb/2009

            % find both solutions by calling asa directly
            r2d = 180/pi;   d2r = 1/r2d;
            [A, B, c] = deal(A*d2r, B*d2r, c*d2r);
            [C1, a1, b1, C2, a2, b2] = SphericalTriangle.asa(A, B, c);
            [C1, a1, b1, C2, a2, b2] = deal(C1*r2d, a1*r2d, b1*r2d, C2*r2d, a2*r2d, b2*r2d);

        end

        %% side-angle-side

        % radians
        function [c1, A1, B1, c2, A2, B2] = sas(a, C, b)
        %SAS   gives both solutions to the side-angle-side problem, in radians.
        %
        %   SAS(a, C, b) returns the remaining unknowns of the spherical triangle,
        %   [c1, A1, B1, c2, A2, B2].
        %
        %   See also sphricaltrig.SASD.

            % first solution
            c1 = SphericalTriangle.acos2(cos(a).*cos(b) + sin(a).*sin(b).*cos(C), C);
            A1 = SphericalTriangle.acos2( (cos(a) - cos(b).*cos(c1))./(sin(b).*sin(c1)), a);
            B1 = SphericalTriangle.acos2( (cos(b) - cos(a).*cos(c1))./(sin(a).*sin(c1)), b);

            % second solution
            c2 = 2*pi - c1;
            A2 = mod(A1 + pi, 2*pi);
            B2 = mod(B1 + pi, 2*pi);

        end

        % degrees
        function [c1, A1, B1, c2, A2, B2] = sasd(a, C, b)
        %SASD   gives both solutions to the side-angle-side problem, in degrees.
        %
        %   SASD(a, C, b) returns the remaining unknowns of the spherical triangle,
        %   [c1, A1, B1, c2, A2, B2].
        %
        %   See also sphricaltrig.SAS.

            % find both solutions by calling sas directly
            r2d = 180/pi;   d2r = 1/r2d;
            [a, C, b] = deal(a*d2r, C*d2r, b*d2r);
            [c1, A1, B1, c2, A2, B2] = SphericalTriangle.sas(a, C, b);
            [c1, A1, B1, c2, A2, B2] = deal(c1*r2d, A1*r2d, B1*r2d, c2*r2d, A2*r2d, B2*r2d);

        end

        %% side-side-angle

        % radians
        function [B1, C1, c1, B2, C2, c2] = ssa(a, b, A)
        %SSA   gives both solutions to the side-side-angle problem, in radians.
        %
        %   SSA(a, b, A) will result in NaNs if the existence condition
        %   |sin b * sin A| <= | sin a |  is not met.
        %
        %   See also SphericalTriangle.SSAD.

            % first solution
            B1 = mod( asin(sin(b).*sin(A)./sin(a)), 2*pi);
            C1 = SphericalTriangle.mal(A, B1, a, b);
            c1 = SphericalTriangle.msl(a, b, A, B1);

            % second solution
            B2 = mod(pi - B1, 2*pi);
            C2 = SphericalTriangle.mal(A, B2, a, b);
            c2 = SphericalTriangle.msl(a, b, A, B2);

            % check constraints
            indices = ( abs(sin(b).*sin(A)) <= abs(sin(a)) );
            B1(indices) = NaN;    C1(indices) = NaN;
            c1(indices) = NaN;    B2(indices) = NaN;
            C2(indices) = NaN;    c2(indices) = NaN;

        end

        % degrees
        function [B1, C1, c1, B2, C2, c2] = ssad(a, b, A)
        %SSAD  gives both solutions to the side-side-angle problem, in degrees.
        %
        %   SSAD(a, b, A) will result in NaNs if the existence condition
        %   |sin b * sin A| <= | sin a |  is not met.
        %
        %   See also SphericalTriangle.SSA.

            % find both solutions by calling ssa directly
            r2d = 180/pi;   d2r = 1/r2d;
            [a, b, A] = deal(a*d2r, b*d2r, A*d2r);
            [B1, C1, c1, B2, C2, c2] = SphericalTriangle.ssa(a, b, A);
            [B1, C1, c1, B2, C2, c2] = deal(B1*r2d, C1*r2d, c1*r2d, B2*r2d, C2*r2d, c2*r2d);

        end

        %% side-side-side

        % radians
        function [A1, B1, C1, A2, B2, C2] = sss(a, b, c)
        %SSS   gives both solutions to the side-side-side problem, in radians.
        %
        %   SSS(a, b, c) results in NaNs for those indices where the existence
        %   condition |pi - a| - |pi - b| <= |pi - c| <= |pi - a| + |pi -b| is not
        %   met.
        %
        %   See also SphericalTriangle.SSSD.

            % first solution
            A1 = SphericalTriangle.acos2( (cos(a) - cos(b).*cos(c))./(sin(b).*sin(c)), a);
            B1 = SphericalTriangle.acos2( (cos(b) - cos(a).*cos(c))./(sin(a).*sin(c)), b);
            C1 = SphericalTriangle.acos2( (cos(c) - cos(a).*cos(b))./(sin(a).*sin(b)), c);

            % second solution
            A2 = 2*pi - A1;
            B2 = 2*pi - B1;
            C2 = 2*pi - C1;

            % check constraints
            indices = ( (abs(pi-a) - abs(pi-b)) <= abs(pi-c) <= (abs(pi-a) + abs(pi-b)) );
            A1(indices) = NaN; B1(indices) = NaN; C1(indices) = NaN;
            A2(indices) = NaN; B2(indices) = NaN; C2(indices) = NaN;

        end

        % degrees
        function [A1, B1, C1, A2, B2, C2] = sssd(a, b, c)
        %SSS   gives both solutions to the side-side-side problem, in degrees.
        %
        %   SSSD(a, b, c) may result in a vector filled with NaNs if the existence
        %   condition |180 - a| - |180 - b| <= |180 - c| <= |180 - a| + |180 - b|
        %   is not met.
        %
        %   See also SphericalTriangle.SSS.

            % find solutions by calling sss
            r2d = 180/pi;   d2r = 1/r2d;
            [a, b, c] = deal(a*d2r, b*d2r, c*d2r);
            [A1, B1, C1, A2, B2, C2] = SphericalTriangle.sss(a, b, c);
            [A1, B1, C1, A2, B2, C2] = deal(A1*r2d, B1*r2d, C1*r2d, A2*r2d, B2*r2d, C2*r2d);

        end

        %% acos2, 4-quadrant arccosine function

        %  radians
        function signedcos = acos2(alpha, beta)
        %ACOS2      4-quadrant arccosine function, in radians.
        %
        %   ACOS2(alpha, beta) computes the four-quadrant arccosine of the angle
        %   [alpha]. For arguments |alpha| > 1, the result is NaN. The resulting
        %   angle is not uniquely determined by alpha, nor by the lengths or
        %   order of the sides of the triangle (as in ATAN2), so an additional
        %   argument [beta] is required. If [beta] < pi/2, the small angle
        %   (0 <= alpha <= pi/2) is returned. If [beta] > pi/2, the large angle
        %   (pi/2 < alpha < pi) is returned.
        %
        %   See also SphericalTriangle.acos2d.

            % compute the hemisphere function
            H               = 2*( mod(beta, 2*pi) < pi ) - 1;
            H(~isreal(phi)) = NaN;

            % compute signed arc-cosine
            signedcos = H .* acos(alpha);

            % set complex results to NaN & take the modulus
            signedcos(~isreal(signedcos)) = NaN;
            signedcos = mod(signedcos, 2*pi);

            % determine valued for zero-valued acos
            ind1     = (signedcos == 0);
            ind2     = (H < 0);                 ind3     = (H > 0);
            indices1 = ((ind1 + ind2) == 2);    indices2 = ((ind1 + ind3) == 2);
            signedcos(indices1) = pi;           signedcos(indices2) = 0;

        end % ACOS2

        % degrees
        function signedcos = acos2d(alpha, beta)
        %ACOS2D      4-quadrant arccosine function, in degrees.
        %
        %   ACOS2D(alpha, beta) computes the four-quadrant arccosine of the amgle
        %   [alpha]. For arguments |alpha| > 1, the result is NaN. The resulting
        %   angle is not uniquely determined by alpha, nor by the lengths or
        %   order of the sides of the triangle (as in ATAN2), so an additional
        %   argument [beta] is required. If [beta] < 180�, the small angle
        %   (0� <= alpha <= 180�) is returned. If [beta] > 180�, the large angle
        %   (180� < alpha < 360�) is returned.
        %
        %   See also SphericalTriangle.acos2.

            % compute 4-quadrant cosine by calling ACOS2 directly
            signedcos = SphericalTriangle.acos2(alpha, beta)*180/pi;

        end

        %% MSL and MAL

        % Middle-side-law
        function c = msl(a, b, A, B)
        %MSL    Computes the missing side in a spherical triangle, in radians.
        %
        %   MSL(a, b, A, B) is the implementation of the Middle Side Law, and
        %   returns the missing angular side c.
        %
        %   See also SphericalTriangle.MAL.

            % sine & cosine c
            % NOTE: denominator not needed
            sinc  = (sin(a).*cos(b).*cos(B) + sin(b).*cos(a).*cos(A));
            cosc  = (cos(a).*cos(b) - sin(a).*sin(b).*cos(A).*cos(B));

            % c is the arctangent of the sine over the cosine
            c = mod( atan2(sinc, cosc), 2*pi);

        end % Middle-side-law

        % Middle-angle-law
        function C = mal(A, B, a, b)
        %MAL    Computes the missing angle in a spherical triangle, in radians.
        %
        %   MAL(A, B, a, b) is the implementation of the Middle Angle Law, and
        %   returns the missing angle C.
        %
        %   See also SphericalTriangle.MSL.

            % sine & cosine of C
            % NOTE: denominator not needed
            sinC  = +sin(A).*cos(B).*cos(b) + sin(B).*cos(A).*cos(a);
            cosC  = -cos(A).*cos(B) + sin(A).*sin(B).*cos(a).*cos(b);

            % C is the arctangent of the ratio of these two
            C = mod( atan2(sinC, cosC), 2*pi);

        end %  Middle-angle-law

    end % public static methods

end % SphericalTriangle class definition


