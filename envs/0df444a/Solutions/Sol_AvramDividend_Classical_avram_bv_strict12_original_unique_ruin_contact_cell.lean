-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_original_unique_ruin_contact_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:42:56.347064+00:00
-- url     : https://prove2.me/submissions/92e6a5ba-f8de-410a-8575-9ee1a89f2633

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal
noncomputable section

theorem solution
    (u : ℕ → ℝ≥0) (τ : ℝ≥0) (hmono : Monotone u) :
    ∀ i j : ℕ,
      (u i < τ ∧ τ ≤ u (i + 1)) →
      (u j < τ ∧ τ ≤ u (j + 1)) → i = j := by
  intro i j hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : i + 1 ≤ j := Nat.succ_le_of_lt hlt
    exact (not_lt_of_ge (hi.2.trans (hmono hle))) hj.1
  · have hle : j + 1 ≤ i := Nat.succ_le_of_lt hgt
    exact (not_lt_of_ge (hj.2.trans (hmono hle))) hi.1
