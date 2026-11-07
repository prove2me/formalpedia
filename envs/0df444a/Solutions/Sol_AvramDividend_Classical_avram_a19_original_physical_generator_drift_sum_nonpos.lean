-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_original_physical_generator_drift_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:42:18.642196+00:00
-- url     : https://prove2.me/submissions/2e691a64-771d-4488-b214-573e89eecfc3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The HJB generator contribution of each genuine stopped physical cell has nonpositive sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by
  let Z : ℕ → ℝ := fun i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  change (∑ i ∈ Finset.range (n + 1),
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i) - q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) ≤ 0
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with h
  · have hGen : X.generator w (Z i) - q * w (Z i) ≤ 0 :=
      (hw_gen (Z i) h.2.1 h.2.2).2
    have hTime : 0 ≤ ((u n (i + 1) : ℝ) - (u n i : ℝ)) := by
      exact sub_nonneg.mpr (by exact_mod_cast hmono n i (Finset.mem_range.mp hi))
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hGen) hTime
  · exact le_refl 0
