-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_col_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:49.661911+00:00
-- url     : https://prove2.me/submissions/b8855e93-ade6-40f4-b554-b402382590af

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_canT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c) (a : Fin n) :
    ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card := by
  by_cases h : a.val < colH mu c
  · apply card_le_card
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact ⟨hb.1, (qb_mem_canT mu c b).2 (lt_of_le_of_lt hb.1 h)⟩
  · calc ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ J.card :=
          card_le_card fun b hb => (mem_filter.1 hb).2
      _ = (canT mu c).1.card := by rw [hJ, (canT mu c).2]
      _ ≤ _ := card_le_card fun b hb => by
          simp only [mem_filter, mem_univ, true_and]
          refine ⟨?_, hb⟩
          have := (qb_mem_canT mu c b).1 hb
          exact Fin.le_def.2 (by omega)
end Formalism.InvariantFactorPaths.ColumnFamilies
