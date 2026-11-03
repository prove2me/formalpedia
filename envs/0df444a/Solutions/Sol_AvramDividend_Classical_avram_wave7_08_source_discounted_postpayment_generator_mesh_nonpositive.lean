-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:40:57.363214+00:00
-- url     : https://prove2.me/submissions/5fb8323d-4ee0-460c-bc96-8e50df588e66

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (N : ℕ) (clock : Fin N → ℝ≥0) (δ : Fin N → ℝ) (ω : Ω)
    (hδ : ∀ i, 0 ≤ δ i)
    (hpos : ∀ i, 0 < x + X.X (clock i) ω - rightLimit D (clock i) ω)
    (hcap : ∀ i, ENNReal.ofReal (x + X.X (clock i) ω -
      rightLimit D (clock i) ω) < C) :
    (∑ i : Fin N,
      (δ i * Real.exp (-(q * (clock i : ℝ)))) *
        (X.generator w (x + X.X (clock i) ω - rightLimit D (clock i) ω) -
         q * w (x + X.X (clock i) ω - rightLimit D (clock i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (hδ i) (le_of_lt (Real.exp_pos _))
  · exact (hw_gen _ (hpos i) (hcap i)).2
