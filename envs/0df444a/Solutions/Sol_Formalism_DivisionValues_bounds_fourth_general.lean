-- Prove2me | solution 1 for Formalism.DivisionValues.bounds_fourth_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:03.481809+00:00
-- url     : https://prove2.me/submissions/8d9b62bd-b51e-4e97-baf3-a5d9a8e7ff7e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_divisor_bounds_first
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_reduction_lemma_first


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : BoundsIVal := by
  intro K _ _ _ _ K0 hcm v0 hv0 n' n D H' hH hdet E Pr hO hK0 hpos P hP A B hA s hs0 hAB G hG0 hG
    w e he
  obtain ⟨hL, hincl⟩ := divisor_bounds_first K n' n H' hH hdet E Pr hO A B hA s hAB G hG
  have h := reduction_lemma_first K K0 hcm v0 hv0 n D (Eᴴ * H' * E) hK0 hpos P hP (cutLat E A) hL (G * s) 1
    (Nat.mul_pos hG0 hs0) (by intro x hx; rw [pow_one]; exact hincl x hx) w e he
  have hG' : (G : K) ≠ 0 := by exact_mod_cast hG0.ne'
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs0.ne'
  rw [Nat.cast_mul, ValuationRepresentative.vw_mul w _ _ hG' hs'] at h
  simpa using h
end Formalism.DivisionValues
