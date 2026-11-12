-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys92_masked_original_BV_generator_drift_jump_grid_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:31:16.446194+00:00
-- url     : https://prove2.me/submissions/5c28e9ef-b792-4785-bc50-e6096ef6a84a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys83_original_BV_discounted_generator_grid_drift_jump_decomp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The physical grid's strict pre-ruin interior mask commutes exactly
with the BV discounted generator, drift and jump decomposition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (n : ℕ)
    (A : ℕ → Prop) [DecidablePred A]
    (z t a : ℕ → ℝ)
    (hGen : ∀ i, A i → X.GeneratorIntegrable w (z i)) :
    (∑ i ∈ Finset.range n, if A i then
      Real.exp (-(q * t i)) *
        (X.generator w (z i) - q * w (z i)) * a i else 0) =
    (∑ i ∈ Finset.range n, if A i then
      Real.exp (-(q * t i)) *
        (X.drift * deriv w (z i) - q * w (z i)) * a i else 0) +
    (∑ i ∈ Finset.range n, if A i then
      (∫ y in Iio (0 : ℝ), Real.exp (-(q * t i)) *
        (w (z i + y) - w (z i)) ∂X.ν) * a i else 0) := by
  classical
  let s : Finset ℕ := (Finset.range n).filter A
  have hs : ∀ i ∈ s, X.GeneratorIntegrable w (z i) := by
    intro i hi
    exact hGen i (Finset.mem_filter.mp hi).2
  have h := avram_bvb_phys83_original_BV_discounted_generator_grid_drift_jump_decomp
    X hBV w q s z t a hs
  simpa only [s, Finset.sum_filter] using h
