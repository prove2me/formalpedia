-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:42.070785+00:00
-- url     : https://prove2.me/submissions/47e5dc93-c79a-469a-a925-151064258b50

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
theorem _root_.solution (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c)
    (h : ∀ a : Fin n, ((univ.filter (· ≤ a)).filter (· ∈ J)).card =
      ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card) : J = (canT mu c).1 := by
  rcases Nat.eq_zero_or_pos (colH mu c) with h0 | hpos
  · have h1 : J = ∅ := card_eq_zero.1 (hJ.trans h0)
    have h2 : (canT mu c).1 = ∅ := card_eq_zero.1 ((canT mu c).2.trans h0)
    rw [h1, h2]
  · have hn := colH_le mu c
    let a : Fin n := ⟨colH mu c - 1, by omega⟩
    have hc : (canT mu c).1 ⊆ (univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1) := fun b hb => by
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨?_, hb⟩
      have := (qb_mem_canT mu c b).1 hb
      exact Fin.le_def.2 (by simp only [a]; omega)
    have h3 : J.card ≤ ((univ.filter (· ≤ a)).filter (· ∈ J)).card := by
      rw [h a, hJ]; exact (canT mu c).2.symm.le.trans (card_le_card hc)
    have h4 : (univ.filter (· ≤ a)).filter (· ∈ J) = J :=
      eq_of_subset_of_card_le (fun b hb => (mem_filter.1 hb).2) h3
    apply eq_of_subset_of_card_le
    · intro b hb
      rw [← h4] at hb
      simp only [mem_filter, mem_univ, true_and] at hb
      have := Fin.le_def.1 hb.1
      exact (qb_mem_canT mu c b).2 (by simp only [a] at this; omega)
    · rw [hJ, (canT mu c).2]
end Formalism.InvariantFactorPaths.ColumnFamilies
