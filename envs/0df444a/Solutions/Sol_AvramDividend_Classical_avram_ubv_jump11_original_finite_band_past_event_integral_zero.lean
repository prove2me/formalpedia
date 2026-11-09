-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_finite_band_past_event_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:38:03.36748+00:00
-- url     : https://prove2.me/submissions/a631798e-f11c-4c5d-a71e-d04a445e3e41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
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
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont s] A) :
    (∫ ω in A, H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hLI, hCZ⟩ :=
    avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
      X s t hst r hsr hrt hShort hLong B hB hFinite
      J hJsource H C hH hHAE hBound
  exact avram_ubv_jump11_past_event_integral_of_condexp_zero
    (𝓕.rightCont s) ((𝓕.rightCont).le s)
    (fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal))
    hLI hCZ A hA
