-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.second_valuation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:18.482392+00:00
-- url     : https://prove2.me/submissions/1466b70c-d3c5-420d-b68f-80f358406421

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_multiplicity_bound_holds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_depth_valuation_sum_holds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_first_bound_holds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_label_sum_plus_holds
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
theorem _root_.solution : Step2Val := by
  intro l k j t w M h i lam xm xp hl hR hxp hh
  have hsum := depth_valuation_sum_holds l k j t w M i lam xm xp hl hR
  have hA1 := first_bound_holds l xm (maxB t w) hl hR.above
  have hLS := label_sum_plus_holds l k t h (i : ℝ) xm xp (maxB t w) hl (Nat.cast_nonneg _) hR.above hR.le hxp hh
  rw [hsum, Nat.cast_sum]
  simp only [Nat.cast_mul]
  have hdisj : Disjoint (Finset.Ioo (maxB t w) xm) (Finset.Ico xm xp) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have := (Finset.mem_Ioo.mp h1).2
    have := (Finset.mem_Ico.mp h2).1
    omega
  have hun : Finset.Ioo (maxB t w) xp = Finset.Ioo (maxB t w) xm ∪ Finset.Ico xm xp := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_Ico]
    have := hR.above
    have := hR.le
    omega
  rw [hun, Finset.sum_union hdisj]
  have h1 : ∑ ct ∈ Finset.Ioo (maxB t w) xm,
        (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤
      (j : ℝ) * ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) +
        ∑ ct ∈ Finset.Ioo (maxB t w) xm,
          min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - maxB t w) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro ct hct
    have hlt := (Finset.mem_Ioo.mp hct).2
    have hm := multiplicity_bound_holds k j t w M i lam xm xp hR ct
    rw [if_pos hlt, if_pos hlt] at hm
    calc (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ)
        ≤ ((j : ℝ) + min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ))) * (vl l (ct - maxB t w) : ℝ) :=
          mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _)
      _ = _ := by ring
  have h2 : ∑ ct ∈ Finset.Ico xm xp,
        (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤
      ∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - maxB t w) : ℝ) := by
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self ?_)
    · intro ct hct
      have hge := (Finset.mem_Ico.mp hct).1
      have hm := multiplicity_bound_holds k j t w M i lam xm xp hR ct
      rw [if_neg (by omega), if_neg (by omega), zero_add] at hm
      exact mul_le_mul_of_nonneg_right (le_trans hm (min_le_right _ _)) (Nat.cast_nonneg _)
    · intro ct _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA : ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) ≤
      (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) := by
    have h3 := hA1.2
    rw [← hA1.1, Nat.cast_sum] at h3
    exact h3
  have hA' := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  unfold labelLHS at hLS
  linarith
end Formalism.CohomologicalDescent.UnitNormBounds
