-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:06:27.709429+00:00
-- url     : https://prove2.me/submissions/69a4bc2e-6d4f-44a4-8d28-13db292e57d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
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
    (hHAE : AEStronglyMeasurable H P)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    Integrable (fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) P ∧
    P[(fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hCountI : Integrable (fun ω => (J ω).toReal) P := by
    simpa only [hJsource] using
      (avram_p2_e_compensator_finite_nu_count_real_integrable
        X s t hst B hB hFinite
        (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
          X s t hst B hB))
  have hDiffI : Integrable (fun ω => (J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P :=
    hCountI.sub (integrable_const _)
  refine ⟨hDiffI.bdd_mul hHAE hBound, ?_⟩
  exact avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
    X s t hst r hsr hrt hShort hLong B hB hFinite
    J hJsource H C hH hBound
