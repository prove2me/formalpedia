-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_ordered_pair_fibre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:49:38.045458+00:00
-- url     : https://prove2.me/submissions/439f623d-6576-4212-b731-5b4292099b84

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_idx_strict_order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal

/-- An ordered original finite-set time pair crosses its second time's uniform cell. -/
theorem solution
    (F : Finset ℝ≥0) (δ : ℝ≥0) (idx : ℝ≥0 → ℕ)
    (hcell : ∀ u ∈ F,
      (idx u : ℝ≥0) * δ < u ∧
      u ≤ (((idx u + 1 : ℕ) : ℝ≥0) * δ))
    (hinj : Set.InjOn idx (F : Set ℝ≥0)) :
    ∀ u ∈ F, ∀ v ∈ F, u < v →
      u ≤ (idx v : ℝ≥0) * δ ∧
      (idx v : ℝ≥0) * δ < v ∧
      v ≤ (((idx v + 1 : ℕ) : ℝ≥0) * δ) := by
  intro u hu v hv huv
  have hord : idx u < idx v :=
    avram_p2_e_compensator_uniform_cell_idx_strict_order
      F δ idx hcell hinj u hu v hv huv
  have hsucc : idx u + 1 ≤ idx v := Nat.succ_le_of_lt hord
  have hcast : ((idx u + 1 : ℕ) : ℝ≥0) ≤ (idx v : ℝ≥0) := by
    exact_mod_cast hsucc
  have hmul : (((idx u + 1 : ℕ) : ℝ≥0) * δ) ≤
      (idx v : ℝ≥0) * δ := mul_le_mul_of_nonneg_right hcast (by positivity)
  exact ⟨le_trans (hcell u hu).2 hmul, (hcell v hv).1, (hcell v hv).2⟩
