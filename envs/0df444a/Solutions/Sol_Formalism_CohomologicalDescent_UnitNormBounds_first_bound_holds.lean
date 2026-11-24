-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.first_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:34.813932+00:00
-- url     : https://prove2.me/submissions/492f5e6e-b982-41a6-94ca-7110ba264589

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_sum_padicVal_shift_eq_factorial
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
theorem _root_.solution : FactorialValuationSum := by
  intro l xm mB hl hlt
  have : Fact l.Prime := ⟨hl⟩
  have hn : (((xm - mB - 1).toNat : ℕ) : ℤ) = xm - mB - 1 := Int.toNat_of_nonneg (by omega)
  constructor
  · have h := sum_padicVal_shift_eq_factorial l mB (xm - mB - 1).toNat
    rw [hn] at h
    have he : mB + 1 + (xm - mB - 1) = xm := by ring
    rw [he] at h
    exact h
  · have h3 := sub_one_mul_padicValNat_factorial (p := l) (xm - mB - 1).toNat
    have h4 : (l - 1) * padicValNat l ((xm - mB - 1).toNat).factorial ≤ (xm - mB - 1).toNat := by
      rw [h3]; exact Nat.sub_le _ _
    have hl2 := hl.two_le
    have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
      linarith
    rw [le_div_iff₀ hl1]
    have h5 : (((l - 1 : ℕ) : ℝ)) * (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤
        (((xm - mB - 1).toNat : ℕ) : ℝ) := by exact_mod_cast h4
    have h6 : (((l - 1 : ℕ) : ℝ)) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h7 : (((xm - mB - 1).toNat : ℕ) : ℝ) = ((xm - mB : ℤ) : ℝ) - 1 := by
      have : ((((xm - mB - 1).toNat : ℕ) : ℤ) : ℝ) = ((xm - mB - 1 : ℤ) : ℝ) := by rw [hn]
      push_cast at this ⊢
      linarith
    rw [h6, h7] at h5
    linarith
end Formalism.CohomologicalDescent.UnitNormBounds
