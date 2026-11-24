-- Prove2me | solution 1 for FairChores.exists_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:56.957487+00:00
-- url     : https://prove2.me/submissions/5fedfa80-f1fe-44b5-819b-0df430921e7a

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution {bill : ℝ} (hb : 0 ≤ bill) (m' : Fin n → ℝ) (h0 : ∀ j, 0 ≤ m' j)
    (hs : bill ≤ ∑ j, m' j) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (∀ j, m j ≤ m' j) ∧ ∑ j, m j = bill := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun j _ => h0 j) : (0:ℝ) ≤ ∑ j, m' j) with heq | hpos
  · refine ⟨m', h0, fun j => le_rfl, ?_⟩
    have : bill = 0 := le_antisymm (by rw [← heq] at hs; exact hs) hb
    rw [this, ← heq]
  · set t : ℝ := bill / ∑ j, m' j with ht
    have ht0 : 0 ≤ t := div_nonneg hb hpos.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hpos]; exact hs
    refine ⟨fun j => t * m' j, fun j => mul_nonneg ht0 (h0 j), fun j => ?_, ?_⟩
    · nlinarith [h0 j]
    · rw [← Finset.mul_sum, ht, div_mul_cancel₀]
      exact ne_of_gt hpos
end FairChores
