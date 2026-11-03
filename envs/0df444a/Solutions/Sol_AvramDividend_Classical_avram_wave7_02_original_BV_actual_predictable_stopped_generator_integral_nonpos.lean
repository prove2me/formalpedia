-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:52:54.813206+00:00
-- url     : https://prove2.me/submissions/8961e06f-eb84-400c-ad59-c25d38b8fe63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Nonpositive integrated original BV generator on any interior predictable
stopped source region with the exact weakened canonical HJB hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (A : Set (ℝ≥0 × Ω))
    (hA : MeasurableSet[𝓕.rightCont.predictable] A)
    (hregion : ∀ p ∈ A,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hInt : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.drift * deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
            (∫ z in Iio (0 : ℝ),
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)))
      A μ) :
    (∫ p in A,
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
          (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) ≤ 0 := by
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with p hp
  obtain ⟨_, hGen, _⟩ :=
    avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
      X hBV q w C hw_gen hw_grad x D p.2 p.1 (hregion p hp)
  exact hGen
