-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:20:17.129888+00:00
-- url     : https://prove2.me/submissions/89c24fbb-2c77-4ae5-8e53-88d2285220cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (B : Set ℝ) (hB : MeasurableSet B) (hFinite : X.ν B < ⊤)
    (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    P[(fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let J2 : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  have hJ2source : ∀ a b ω, J2 a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B) := by
    intro a b ω
    rfl
  have hJ2meas : Measurable (J2 s t) := by
    simpa only [J2] using
      (avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X s t hst B hB)
  have hCountI : Integrable (fun ω => (J ω).toReal) P := by
    simpa only [hJsource] using
      (avram_p2_e_compensator_finite_nu_count_real_integrable
        X s t hst B hB hFinite
        (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
          X s t hst B hB))
  have hYint : Integrable (fun ω => (J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P :=
    hCountI.sub (integrable_const _)
  have hCenter : P[(fun ω => (J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
    simpa only [hJsource, J2] using
      (avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
        X s t r hsr hrt B hB J2 hJ2source hShort hLong
        (ne_top_of_lt hFinite) hJ2meas)
  exact avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
    X s t B J hJsource
    (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    hYint hCenter H C hH hBound
