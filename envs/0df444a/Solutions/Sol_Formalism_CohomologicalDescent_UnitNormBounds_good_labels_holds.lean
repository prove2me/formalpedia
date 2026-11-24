-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.good_labels_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:13.315474+00:00
-- url     : https://prove2.me/submissions/7479d47f-3d30-42fa-973f-ac148c8264af

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_rowStart_rev_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution : GoodLabels := by
  intro k j t w M i lam hb tau htau b col h1 h2
  have hU := rowStart_rev_eq k j t w M lam hb b
  have hw := hb (Fin.rev b)
  have hd : dual M lam b = M - lam (Fin.rev b) := rfl
  obtain ⟨_, _, _, _, hbox⟩ := Finset.mem_filter.mp htau
  constructor
  · by_contra hcon
    unfold boxesOfContent at hbox
    rw [Finset.card_eq_zero] at hbox
    have hmem : b ∈ Finset.univ.filter fun a : Fin (k + j) =>
        (dual M lam a : ℤ) ≤ ((M - w : ℕ) : ℤ) + (a.val : ℤ) ∧
          ((M - w : ℕ) : ℤ) + (a.val : ℤ) < (tau a : ℤ) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · omega
      · unfold label maxB at hcon
        omega
    rw [hbox] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · unfold label
    omega
end Formalism.CohomologicalDescent.UnitNormBounds
