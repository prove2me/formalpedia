-- Prove2me | solution 1 for Formalism.G0.TopsCount.condProb_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:40.739402+00:00
-- url     : https://prove2.me/submissions/6c07a3ed-e2cc-461b-aa54-7d11d18fa1a0

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
import Theorems.Thm_Formalism_G0_TopsCount_sum_ite_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsCount
namespace Formalism.G0.TopsCount
theorem _root_.solution (m : ℕ) (δ : ℝ) (N : ℕ) :
    condProb (m + 1) δ (fun T => T.card < N) = A m δ (N - 1) := by
  classical
  unfold condProb
  have h0 : (0 : ℕ) ∉ (range (m + 1)).erase 0 := notMem_erase 0 _
  have hr : range (m + 1) = insert 0 ((range (m + 1)).erase 0) :=
    (insert_erase (by simp)).symm
  rw [hr, sum_powerset_insert h0]
  beta_reduce
  rw [Finset.sum_eq_zero, zero_add]
  swap
  · intro t ht
    rw [if_neg]
    rintro ⟨h, _⟩
    exact h0 (mem_powerset.1 ht h)
  rw [Finset.sum_congr rfl (g := fun t : Finset ℕ =>
    (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0) t.card)]
  swap
  · intro t ht
    have ht0 : (0 : ℕ) ∉ t := fun h => h0 (mem_powerset.1 ht h)
    rw [card_insert_of_notMem ht0]
    beta_reduce
    by_cases hN : t.card + 1 < N
    · rw [if_pos ⟨mem_insert_self 0 t, hN⟩, if_pos (by omega),
        show t.card + 1 - 1 = t.card by omega, show m + 1 - (t.card + 1) = m - t.card by omega]
    · rw [if_neg (fun h => hN h.2), if_neg (by omega)]
  rw [sum_powerset_apply_card (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0)]
  have hcard : ((range (m + 1)).erase 0).card = m := by
    rw [card_erase_of_mem (by simp), card_range]; rfl
  rw [hcard, ← sum_ite_lt]
  apply sum_congr rfl
  intro j _
  rw [nsmul_eq_mul]
  by_cases hj : j < N - 1
  · rw [if_pos hj, if_pos hj]; unfold a; ring
  · rw [if_neg hj, if_neg hj, mul_zero]
end Formalism.G0.TopsCount
