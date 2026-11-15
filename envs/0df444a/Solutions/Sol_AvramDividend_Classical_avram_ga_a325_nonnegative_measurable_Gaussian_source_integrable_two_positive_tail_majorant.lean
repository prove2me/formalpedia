-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:17:12.618223+00:00
-- url     : https://prove2.me/submissions/674062ab-7cce-4518-aae6-44ac451575f5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Integrability under two nonnegative integrable majorants. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F S Q : Ω → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hFm : AEStronglyMeasurable F P)
    (hSI : Integrable S P) (hQI : Integrable Q P)
    (hFpos : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hSpos : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hQpos : ∀ᵐ ω ∂P, 0 ≤ Q ω)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ c*S ω + d*Q ω) :
    Integrable F P := by
  have hI : Integrable (fun ω => c*S ω + d*Q ω) P :=
    (hSI.const_mul c).add (hQI.const_mul d)
  apply Integrable.mono' hI hFm
  filter_upwards [hFpos, hSpos, hQpos, hUpper] with ω hf hs hq hu
  have hm : 0 ≤ c*S ω + d*Q ω :=
    add_nonneg (mul_nonneg hc hs) (mul_nonneg hd hq)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hm] using hu
