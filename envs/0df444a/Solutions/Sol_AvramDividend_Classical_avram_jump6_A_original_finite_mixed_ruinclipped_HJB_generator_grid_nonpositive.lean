-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finite_mixed_ruinclipped_HJB_generator_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:42:17.392176+00:00
-- url     : https://prove2.me/submissions/af08e8a7-4f54-4574-b47f-139c26a5d592

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (m : ℕ) (t : ℕ → ℝ≥0) (active : ℕ → Bool)
    (hTimes : ∀ i ∈ Finset.range m, t i ≤ t (i + 1))
    (hInterior : ∀ i ∈ Finset.range m, active i = true →
      0 < riskProcess X x D (t i) ω ∧
      ENNReal.ofReal (riskProcess X x D (t i) ω) < C) :
    (∑ i ∈ Finset.range m,
       if active i then
          Real.exp (-(q * (t i : ℝ))) *
            ((t (i + 1) : ℝ) - (t i : ℝ)) *
             (X.generator w (riskProcess X x D (t i) ω) -
                q * w (riskProcess X x D (t i) ω))
       else 0) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hActive
  · obtain ⟨hy, hC⟩ := hInterior i hi hActive
    have hGenerator := (hw_gen _ hy hC).2
    have hStep : 0 ≤ (t (i + 1) : ℝ) - (t i : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hTimes i hi)
    have hWeight : 0 ≤
        Real.exp (-(q * (t i : ℝ))) *
          ((t (i + 1) : ℝ) - (t i : ℝ)) :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) hStep
    exact mul_nonpos_of_nonneg_of_nonpos hWeight hGenerator
  · exact le_refl 0
