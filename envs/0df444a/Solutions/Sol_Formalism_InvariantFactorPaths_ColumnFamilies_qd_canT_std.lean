-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_canT_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:31.10166+00:00
-- url     : https://prove2.me/submissions/98433c3b-f475-4d15-b6b6-125063f9007b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  have hle : colH mu ((c : ℤ) + 1) ≤ colH mu c := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 hle⟩, rfl⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
