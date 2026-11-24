-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.label_sum_plus_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:30.994102+00:00
-- url     : https://prove2.me/submissions/40518472-0e47-40be-a64d-647a93340c13

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_labelLHS_shift_to_zero
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_indexIntegral_shift
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_indexIntegral_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_gated_min_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_labelSumLe_holds
import Theorems.Thm_Formalism_CohomologicalDescent_label_vl_zero_small
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution : LabelSumPlus := by
  intro l k t h i xm xp mB hl hi hmx hxx hxp hh
  by_cases hlh : h < l
  · have hlhZ : (h : ℤ) < (l : ℤ) := by exact_mod_cast hlh
    have hz : ∀ ct : ℤ, mB < ct → ct ≤ xp → (vl l (ct - mB) : ℝ) = 0 := by
      intro ct h1 h2
      rw [label_vl_zero_small (by omega) (by omega)]
      simp
    have hL : labelLHS l k t i xm xp mB = 0 := by
      unfold labelLHS
      rw [Finset.sum_eq_zero (fun ct hct => by
            rw [hz ct (by have := Finset.mem_Icc.mp hct; omega) (Finset.mem_Icc.mp hct).2, mul_zero]),
          Finset.sum_eq_zero (fun ct hct => by
            rw [hz ct (Finset.mem_Ioo.mp hct).1 (by have := Finset.mem_Ioo.mp hct; omega), mul_zero]),
          add_zero]
    rw [hL]
    unfold labelSumBoundPos harm
    rw [if_pos hlh, add_zero]
    refine add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg ?_ (Nat.cast_nonneg _))
      (indexIntegral_nonneg _ _ _ _))) (gated_min_nonneg l k t i hi _)
    exact_mod_cast (by omega : (0 : ℤ) ≤ xp - xm)
  · have h1 := labelSumLe_holds l k t h i (xm - mB) (xp - mB) 0 hl hi le_rfl (by omega) (by omega) (by omega) hh
      (by omega)
    rw [← labelLHS_shift_to_zero] at h1
    unfold labelSumBound at h1
    unfold labelSumBoundPos harm
    rw [if_neg hlh]
    have e : xp - mB - (xm - mB) = xp - xm := by ring
    rw [indexIntegral_shift, e] at h1
    simp only [sub_zero] at h1
    exact h1
end Formalism.CohomologicalDescent.UnitNormBounds
