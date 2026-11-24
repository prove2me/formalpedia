-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.trForm_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:14.974985+00:00
-- url     : https://prove2.me/submissions/382d2026-a49d-4a9f-b0b2-36e5a1d7f93c

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_trForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution (h : U →ₗ[E] U →ₗ⋆[E] E) (hnd : ∀ x : U, (∀ y : U, h x y = 0) → x = 0) :
    ∀ x, (∀ y, trForm h x y = 0) → x = 0 := by
  intro x hx
  apply hnd
  intro y
  apply (traceForm_nondegenerate ℚ E).1
  intro e
  rw [Algebra.traceForm_apply]
  have h1 := hx (star e • y)
  rw [trForm_apply, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm] at h1
  exact h1
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
