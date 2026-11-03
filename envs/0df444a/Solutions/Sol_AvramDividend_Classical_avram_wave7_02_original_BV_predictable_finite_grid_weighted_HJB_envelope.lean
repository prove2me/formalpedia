-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_predictable_finite_grid_weighted_HJB_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:47:15.829981+00:00
-- url     : https://prove2.me/submissions/0977feb5-8058-42e4-8b77-f911bd509ac8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_finite_grid_weighted_HJB_envelope_scoped
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Bridge the original weighted finite-grid generator and Stieltjes inequality from the proved scoped form through a named intermediate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : Finset ℝ≥0) (a b : ℝ≥0 → ℝ)
    (ha : ∀ t ∈ u, 0 ≤ a t)
    (hb : ∀ t ∈ u, 0 ≤ b t)
    (hregion : ∀ t ∈ u,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (∑ t ∈ u,
      (a t * (Real.exp (-(q * (t : ℝ))) *
        (X.drift * deriv w (Y t) +
          (∫ z in Iio (0 : ℝ),
            w (Y t + z) - w (Y t) ∂X.ν) - q * w (Y t))) +
      b t * (Real.exp (-(q * (t : ℝ))) *
        (1 - deriv w (Y t))))) ≤ 0 := by
  have hScoped :=
    avram_wave7_02_original_BV_predictable_finite_grid_weighted_HJB_envelope_scoped
      X hBV q w C hw_gen hw_grad x D ω u a b ha hb hregion
  simpa only [] using hScoped
