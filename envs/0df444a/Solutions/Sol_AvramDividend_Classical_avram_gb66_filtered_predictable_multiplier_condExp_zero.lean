-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb66_filtered_predictable_multiplier_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:27:09.831397+00:00
-- url     : https://prove2.me/submissions/cfdc93f2-2728-4acf-ad0b-6ac692d0ccb6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Pull a predictable multiplier out of a zero conditional mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓢 : MeasurableSpace Ω) (H Q : Ω → ℝ)
    (hH : StronglyMeasurable[𝓢] H)
    (hHQ : Integrable (fun ω => H ω * Q ω) P)
    (hQ : Integrable Q P)
    (hQzero : P[Q | 𝓢] =ᵐ[P] (fun _ => 0)) :
    P[(fun ω => H ω * Q ω) | 𝓢] =ᵐ[P] (fun _ => 0) := by
  have hpull :
      P[(fun ω => H ω * Q ω) | 𝓢] =ᵐ[P]
        (fun ω => H ω * P[Q | 𝓢] ω) :=
    condExp_mul_of_stronglyMeasurable_left hH hHQ hQ
  filter_upwards [hpull, hQzero] with ω hp hq
  simpa only [hq, mul_zero] using hp
