-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:34:07.871961+00:00
-- url     : https://prove2.me/submissions/d5eaed8c-7668-4912-ab65-248b94ca769e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuinely random bounded coefficient from the original predictable
past can be pulled through the conditional expectation of the centred
actual original Lévy finite-band jump count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (rate : ℝ≥0∞)
    (hYint : Integrable (fun ω => (J ω).toReal - rate.toReal) P)
    (hYcenter :
      P[(fun ω => (J ω).toReal - rate.toReal) | 𝓕.rightCont s] =ᵐ[P] 0)
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    P[(fun ω => H ω * ((J ω).toReal - rate.toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  have hm : 𝓕.rightCont s ≤ mΩ := (𝓕.rightCont).le s
  have hPull := condExp_stronglyMeasurable_mul_of_bound
    hm hH hYint C hBound
  filter_upwards [hPull, hYcenter] with ω he hc
  calc
    P[(fun x => H x * ((J x).toReal - rate.toReal)) |
      𝓕.rightCont s] ω =
        H ω * P[(fun x => (J x).toReal - rate.toReal) |
          𝓕.rightCont s] ω := he
    _ = 0 := by simpa only [hc, Pi.zero_apply, mul_zero]
