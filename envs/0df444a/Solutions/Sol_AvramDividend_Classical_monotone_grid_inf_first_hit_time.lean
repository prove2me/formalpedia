-- Prove2me | solution 1 for AvramDividend.Classical.monotone_grid_inf_first_hit_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:18:05.383051+00:00
-- url     : https://prove2.me/submissions/58a300d8-50a0-4bfe-85ae-184f62cce167

import Mathlib.Data.Nat.Find
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (u : ℕ → ℝ) (s : Set ℝ) [DecidablePred (fun k : ℕ => u k ∈ s)]
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (h : ∃ j : ℕ, u j ∈ s) :
    (⨅ k : ℕ, if u k ∈ s then (clock k : ℝ≥0∞) else ∞) =
      (clock (Nat.find h) : ℝ≥0∞) := by
  classical
  have hj : u (Nat.find h) ∈ s := Nat.find_spec h
  apply le_antisymm
  · calc
      (⨅ k : ℕ, if u k ∈ s then (clock k : ℝ≥0∞) else ∞) ≤
          (if u (Nat.find h) ∈ s
            then (clock (Nat.find h) : ℝ≥0∞) else ∞) :=
        iInf_le _ (Nat.find h)
      _ = (clock (Nat.find h) : ℝ≥0∞) := if_pos hj
  · apply le_iInf
    intro k
    by_cases hk : u k ∈ s
    · rw [if_pos hk]
      exact_mod_cast (hc (Nat.find_le (h := h) hk))
    · rw [if_neg hk]
      exact le_top
