-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:01:54.085829+00:00
-- url     : https://prove2.me/submissions/be2fb146-059a-4d1a-8309-ab01a963d25b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_public_original_mark_marginal_tonelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original jump-intensity measure governing every time horizon also
integrates every nonnegative measurable mark test by its genuine unit-time
intrinsic counting kernel, with no compensator hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ σ : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * σ B) ∧
      (∀ (f : ℝ → ℝ), Measurable f →
        (∫⁻ y, ENNReal.ofReal (f y) ∂σ) =
          (∫⁻ ω, ∫⁻ p in (Ioc 0 (1 : ℝ≥0) ×ˢ (Set.univ : Set ℝ)),
            ENNReal.ofReal (f p.2) ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P)) ∧
      (∀ ε : ℝ, 0 < ε → σ (Iic (-ε)) < ⊤) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        σ B = σ (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite σ := by
  obtain ⟨σ, hRate, hBand, hSupport, hSigma⟩ :=
    avram_p2_c_borel_original_intrinsic_intensity_measure_complete X
  refine ⟨σ, hRate, ?_, hBand, hSupport, hSigma⟩
  intro f hf
  obtain ⟨ρ, hρ, hPos⟩ :=
    avram_p2_a_assist_public_original_mark_marginal_tonelli
      X (1 : ℝ≥0) (fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hf)
  have hEq : ρ = σ := by
    apply Measure.ext
    intro B hB
    simpa using (hρ B hB).trans (hRate 1 B hB)
  simpa [hEq] using hPos
