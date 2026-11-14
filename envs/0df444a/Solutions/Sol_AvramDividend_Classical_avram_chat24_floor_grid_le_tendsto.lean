-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_floor_grid_le_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:38:23.714979+00:00
-- url     : https://prove2.me/submissions/aaeca7e6-767c-496e-8c9a-136963ab1ac6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution (t : ℝ≥0) :
    let q : ℕ → ℝ≥0 := fun n =>
      ⟨(⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1), by positivity⟩
    (∀ n, q n ≤ t) ∧ Tendsto q atTop (nhds t) := by
  let q : ℕ → ℝ≥0 := fun n =>
    ⟨(⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1), by positivity⟩
  change (∀ n, q n ≤ t) ∧ Tendsto q atTop (nhds t)
  have hqle (n : ℕ) : q n ≤ t := by
    change (⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1) ≤ (t : ℝ)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    exact Nat.floor_le (by positivity)
  refine ⟨hqle, ?_⟩
  have hqlo (n : ℕ) : (t : ℝ) - 1 / ((n : ℝ) + 1) ≤ (q n : ℝ) := by
    change (t : ℝ) - 1 / ((n : ℝ) + 1) ≤
      (⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1)
    rw [sub_le_iff_le_add, ← add_div]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      (Nat.lt_floor_add_one _).le
  have he : Tendsto (fun n => (t : ℝ) - (q n : ℝ)) atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hqle n))
      (fun n => by linarith [hqlo n]) tendsto_one_div_add_atTop_nhds_zero_nat
  have hr : Tendsto (fun n => (q n : ℝ)) atTop (nhds (t : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (nhds (t : ℝ)) :=
      tendsto_const_nhds
    simpa only [sub_sub_cancel, sub_zero] using hc.sub he
  exact tendsto_subtype_rng.2 hr
