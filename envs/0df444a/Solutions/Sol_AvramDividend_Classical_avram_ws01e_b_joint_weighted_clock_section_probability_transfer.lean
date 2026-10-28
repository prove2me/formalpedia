-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_joint_weighted_clock_section_probability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:21:53.63728+00:00
-- url     : https://prove2.me/submissions/f6fb74d0-055a-4892-8dc1-0f67ab68c00a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_joint_clock_event_fibrewise_disintegration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Equal density-weighted clock fibres yield equal probabilities under the
genuine joint random-terminal likelihood, not merely under a product law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    (η : Measure ℝ) [SFinite η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (A B : Set (Ω × ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFibre : ∀ t : ℝ,
      (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | (ω, t) ∈ A} =
      (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | (ω, t) ∈ B}) :
    ((P.prod η).withDensity D) A =
      ((P.prod η).withDensity D) B := by
  rw [esscher_joint_clock_event_fibrewise_disintegration
      P η D hD A hA,
    esscher_joint_clock_event_fibrewise_disintegration
      P η D hD B hB]
  exact lintegral_congr_ae (Filter.Eventually.of_forall hFibre)
