-- Prove2me | solution 1 for AvramDividend.Classical.avram_b237_original_ruinclipped_physical_gaussian_jump_mesh_HJB_drift_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:06:34.752505+00:00
-- url     : https://prove2.me/submissions/f0aa2059-4156-43b4-8301-606c86e4087d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let H : ℕ → ℝ := fun i =>
      let z := riskProcess X x D (s i) ω
      if s i < σ ω ∧ 0 < z ∧ ENNReal.ofReal z < C then
        (Δ : ℝ) * Real.exp (-(q * (s i : ℝ))) *
          (X.generator w z - q * w z)
      else 0
    (Finset.range m).sum H ≤ 0 := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let H : ℕ → ℝ := fun i =>
    let z := riskProcess X x D (s i) ω
    if s i < σ ω ∧ 0 < z ∧ ENNReal.ofReal z < C then
      (Δ : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (X.generator w z - q * w z)
    else 0
  change (Finset.range m).sum H ≤ 0
  apply Finset.sum_nonpos
  intro i hi
  change (if s i < σ ω ∧ 0 < riskProcess X x D (s i) ω ∧
        ENNReal.ofReal (riskProcess X x D (s i) ω) < C
      then (Δ : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (X.generator w (riskProcess X x D (s i) ω) -
          q * w (riskProcess X x D (s i) ω))
      else 0) ≤ 0
  split_ifs with h
  · have hgen := (hw_gen _ h.2.1 h.2.2).2
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by positivity) (le_of_lt (Real.exp_pos _))) hgen
  · exact le_refl 0
