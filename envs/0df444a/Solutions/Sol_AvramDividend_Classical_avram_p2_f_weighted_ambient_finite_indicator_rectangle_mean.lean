-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_ambient_finite_indicator_rectangle_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:39:27.581001+00:00
-- url     : https://prove2.me/submissions/81d48235-2c55-426a-ba05-994f341b5399

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Finite nonnegative simple past-event combinations inherit an exact
ambient rectangle count first moment, conditional on that first moment. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (r : ℝ≥0∞) (S : Finset ι)
    (A : ι → Set Ω) (c : ι → ℝ≥0∞)
    (hA : ∀ i ∈ S, MeasurableSet[mPast] (A i))
    (hEvent : ∀ E : Set Ω, MeasurableSet[mPast] E →
      (∫⁻ ω in E, N ω ∂μ) = μ E * r) :
    (∫⁻ ω, S.sum (fun i => c i * (A i).indicator N ω) ∂μ) =
    S.sum (fun i => c i * (μ (A i) * r)) := by
  have hAmbient (i : ι) (hi : i ∈ S) : MeasurableSet[mΩ] (A i) :=
    hm (A i) (hA i hi)
  have hSummand (i : ι) (hi : i ∈ S) :
      Measurable[mΩ] (fun ω => c i * (A i).indicator N ω) :=
    measurable_const.mul (hN.indicator (hAmbient i hi))
  calc
    (∫⁻ ω, S.sum (fun i => c i * (A i).indicator N ω) ∂μ)
        = S.sum (fun i => ∫⁻ ω, c i * (A i).indicator N ω ∂μ) := by
            simpa using (lintegral_finset_sum S (fun i hi => hSummand i hi))
    _ = S.sum (fun i => c i * (μ (A i) * r)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [lintegral_const_mul (c i) (hN.indicator (hAmbient i hi)),
            lintegral_indicator (hAmbient i hi), hEvent (A i) (hA i hi)]
