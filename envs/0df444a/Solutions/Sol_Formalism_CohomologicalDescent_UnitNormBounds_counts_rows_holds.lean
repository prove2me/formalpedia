-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.counts_rows_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:58.274263+00:00
-- url     : https://prove2.me/submissions/2f5c423e-2d7d-43ad-9dde-51c40946adeb

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_rowStart_rev_eq
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_content_label_eq
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_card_filter_not_rev_lt_le
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
theorem _root_.solution : CountsRows := by
  intro k j t w M i lam xm xp hR tau _ ct
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  unfold boxesOfLabel boxesOfContent cloudBoxes
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun a : Fin (k + j) =>
      (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ))
      (fun b : Fin (k + j) => (Fin.rev b).val < k), add_comm]
  rw [Finset.filter_filter, Finset.filter_filter]
  refine Nat.add_le_add ?_ (le_of_eq ?_)
  · split_ifs with hct
    · refine le_trans (le_of_eq ?_) (card_filter_not_rev_lt_le k j (fun a : Fin (k + j) =>
        (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ)))
      congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro b _ ⟨⟨h1, _⟩, h3⟩
      have hU := rowStart_rev_eq k j t w M lam hb b
      have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
      have hr := hR.rest (Fin.rev b) (by omega)
      omega
  · congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
end Formalism.CohomologicalDescent.UnitNormBounds
