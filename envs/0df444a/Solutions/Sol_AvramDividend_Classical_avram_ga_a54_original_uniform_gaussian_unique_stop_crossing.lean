-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a54_original_uniform_gaussian_unique_stop_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:24:03.298724+00:00
-- url     : https://prove2.me/submissions/3ad586cb-a41e-443f-93ca-74192457db27

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) (hm : 0 < m) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 1 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by
  cases m with
  | zero => exact False.elim (Nat.lt_irrefl 0 hm)
  | succ k =>
    have h := avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
      n k ρ hρn hρpos
    norm_num [Nat.succ_eq_add_one, Nat.cast_add, add_assoc] at h
    norm_num [Nat.succ_eq_add_one, Nat.cast_add, add_assoc]
    exact h
