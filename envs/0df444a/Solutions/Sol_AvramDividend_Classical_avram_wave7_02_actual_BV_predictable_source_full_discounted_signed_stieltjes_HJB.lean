-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_actual_BV_predictable_source_full_discounted_signed_stieltjes_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:47:00.721577+00:00
-- url     : https://prove2.me/submissions/f6f9a085-6062-416d-b751-c69c5c7d7646

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual original BV predictable physical generator and the diffuse
real dividend-measure density have a nonpositive discounted joint HJB integral
on any exactly localised interior stopped region. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hIGen : IntegrableOn
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
      E μ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAclock : A ⊆ paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (hAregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hIDiv : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω)) :
    (∫ p in E,
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
          (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) +
    (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by
  have hSource :=
    avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
      X hBV q w C hw_gen hw_grad x D μ E hEm hEregion hIGen
  have hDiv : (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by
    apply MeasureTheory.integral_nonpos_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hAm] with t ht
    obtain ⟨ht0, htC⟩ := hAregion t ht
    have hSlope : 1 - deriv w (riskProcess X x D t.toNNReal ω) ≤ 0 :=
      sub_nonpos.mpr (hw_grad _ ht0 htC)
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) hSlope
  exact add_nonpos hSource hDiv
