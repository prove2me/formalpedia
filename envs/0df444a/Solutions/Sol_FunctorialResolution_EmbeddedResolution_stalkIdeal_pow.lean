-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:51.855801+00:00
-- url     : https://prove2.me/submissions/613704b4-5711-4027-ae83-af497e15aa33

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem idealSheafData_one_eq_top {X : Scheme.{u}} :
    (1 : X.IdealSheafData) = ⊤ := rfl
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) (n : ℕ) (x : X) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, idealSheafData_one_eq_top, stalkIdeal_top, Ideal.one_eq_top]
  | succ n ih =>
    rw [pow_succ, pow_succ, stalkIdeal_mul, ih]
end FunctorialResolution.EmbeddedResolution
