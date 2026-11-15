-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_discounted_HJB_generator_physical_strict_interior_finite_grid_sum_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:57:29.033206+00:00
-- url     : https://prove2.me/submissions/46f9c63a-e41f-4d97-9e85-e92a8ebe2366

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (y : ι → ℝ)
    (hTimes : ∀ i ∈ S, s i ≤ t i)
    (hInterior : ∀ i ∈ S,
      0 < y i ∧ ENNReal.ofReal (y i) < C) :
    (∑ i ∈ S, Real.exp (-(q * (s i : ℝ))) *
      ((t i : ℝ) - (s i : ℝ)) *
        (X.generator w (y i) - q * w (y i))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hElapsed : (0 : ℝ) ≤ (t i : ℝ) - (s i : ℝ) := by
    have hReal : (s i : ℝ) ≤ (t i : ℝ) := by
      exact_mod_cast hTimes i hi
    linarith
  have hDisc : 0 ≤ Real.exp (-(q * (s i : ℝ))) :=
    (Real.exp_pos _).le
  have hGen : X.generator w (y i) - q * w (y i) ≤ 0 :=
    (hgen (y i) (hInterior i hi).1 (hInterior i hi).2).2
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hDisc hElapsed) hGen
