-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_predictable_full_negative_source_compensator_clock_integral_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:53:11.019901+00:00
-- url     : https://prove2.me/submissions/fbc69a49-6937-46fb-8672-574c464b2717

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual original negative-Levy-mark compensator on the complete
predictable space-time clock is nonpositive after discount on any measurable
interior stopped set. This covers marks jumping below ruin; separate original
jump-measure compensation is still required for stochastic verification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hMarkInt : ∀ p ∈ E,
      IntegrableOn (fun z : ℝ =>
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))
        (Iio 0) X.ν)
    (hClockInt : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν))
      E μ) :
    (∫ p in E,
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ),
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν)
       ∂μ) ≤ 0 := by
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hEm] with p hp
  exact (avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
    X hBV C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
    x D p.2 p.1 (hEregion p hp) (hMarkInt p hp) q).2
