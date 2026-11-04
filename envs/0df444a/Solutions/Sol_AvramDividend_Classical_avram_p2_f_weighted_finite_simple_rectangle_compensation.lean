-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_finite_simple_rectangle_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:43:15.583464+00:00
-- url     : https://prove2.me/submissions/ded17bc8-0ae4-4004-8b04-dece14fe120e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_indicator_to_general_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Finite predictable-step compensation from genuinely established
event rectangle identities via the accepted generic ENNReal induction. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (μ : Measure Ω) (S : Finset ι)
    (N H : ι → Ω → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (hN : ∀ i ∈ S, Measurable (N i))
    (hH : ∀ i ∈ S, Measurable[mPast] (H i))
    (hEvent : ∀ i ∈ S, ∀ A : Set Ω, MeasurableSet[mPast] A →
      (∫⁻ ω in A, N i ω ∂μ) = μ A * r i) :
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂μ) =
    S.sum (fun i => (∫⁻ ω, H i ω ∂μ) * r i) := by
  have hOne (i : ι) (hi : i ∈ S) :
      (∫⁻ ω, H i ω * N i ω ∂μ) = (∫⁻ ω, H i ω ∂μ) * r i :=
    @AvramDividend.Classical.avram_p2_f_weighted_indicator_to_general_lintegral
      Ω mΩ mPast hm μ (N i) (hN i hi) (r i) (hEvent i hi) (H i) (hH i hi)
  have hProd (i : ι) (hi : i ∈ S) :
      Measurable (fun ω => H i ω * N i ω) :=
    (hH i hi).mul (hN i hi)
  calc
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂μ)
        = S.sum (fun i => ∫⁻ ω, H i ω * N i ω ∂μ) := by
            simpa using (lintegral_finset_sum S (fun i hi => hProd i hi))
    _ = S.sum (fun i => (∫⁻ ω, H i ω ∂μ) * r i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hOne i hi
