-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_discounted_interior_HJB_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:25:52.104771+00:00
-- url     : https://prove2.me/submissions/0fbc9f54-0e12-4f7a-8610-c34a6cc0fad8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Original source HJB drift, discounted on finite grid cells: only strict
interior states contribute; zero and cap contact remain separately owned. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (Z : ℕ → Ω → ℝ) :
    ∀ ω,
      (∑ i ∈ Finset.range n,
        if 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i ω) - q * w (Z i ω)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) ≤ 0 := by
  intro ω
  apply Finset.sum_nonpos
  intro i hi
  by_cases hinside : 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C
  · simp only [if_pos hinside]
    have hi' : i < n := Finset.mem_range.mp hi
    have hdelta : 0 ≤ (u (i + 1) : ℝ) - (u i : ℝ) :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hGrid i hi'))
    have hgen : X.generator w (Z i ω) - q * w (Z i ω) ≤ 0 :=
      (hw_gen _ hinside.1 hinside.2).2
    have hexp : 0 ≤ Real.exp (-(q * (u i : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hexp hgen) hdelta
  · simp only [if_neg hinside, le_refl]
