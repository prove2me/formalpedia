-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:14:23.334289+00:00
-- url     : https://prove2.me/submissions/f85b88d2-c910-4eba-b7f9-3d28d237eb10

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Eventually every natural-indexed floor sample is later than a strict ruin time. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (t : ℝ≥0) (τ : ℝ≥0∞)
    (hτ : τ < (t : ℝ≥0∞)) :
    Filter.Eventually
      (fun n : ℕ => ¬ ((Real.toNNReal
        (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) /
          ((n : ℝ) + 2)) : ℝ≥0∞) < τ))
      Filter.atTop := by
  let v : ℕ → ℝ := fun n => T *
    (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)
  let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n)
  have hfloor := avram_bvb_b21_original_uniform_floor_samples_converge_from_left
    T (t : ℝ) hT t.property
  have hs : Tendsto s atTop (𝓝 t) := by
    have hc := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hfloor.2
    rw [Real.toNNReal_coe] at hc
    change Tendsto (Real.toNNReal ∘ v) atTop (𝓝 t)
    exact hc
  have hsE : Tendsto (fun n => (s n : ℝ≥0∞)) atTop (𝓝 (t : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto t).comp hs
  have hAfter : ∀ᶠ n in atTop, τ < (s n : ℝ≥0∞) :=
    hsE.eventually (Ioi_mem_nhds hτ)
  have hConclusion : ∀ᶠ n : ℕ in atTop, ¬ ((s n : ℝ≥0∞) < τ) := by
    filter_upwards [hAfter] with n hn
    exact not_lt.mpr (le_of_lt hn)
  exact hConclusion
