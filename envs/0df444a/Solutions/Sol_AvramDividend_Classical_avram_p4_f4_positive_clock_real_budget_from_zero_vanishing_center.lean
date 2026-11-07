-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_positive_clock_real_budget_from_zero_vanishing_center
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:37:26.939789+00:00
-- url     : https://prove2.me/submissions/faf10ca5-1f58-4919-b3a9-a2195e6a5e81

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_centered_integral_of_zero_complement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
/-- The original zero-clock vanishing source gives a conditional budget without normalising the probability event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (S : Set Ω) (hS : MeasurableSet S) (F M : Ω → ℝ) (B : ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hZeroOutside : ∀ᵐ ω ∂P, ω ∉ S → M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ B + M ω) :
    (∫ ω in S, F ω ∂P) ≤ (∫ ω in S, B ∂P) := by
  have hZeroS : (∫ ω in S, M ω ∂P) = 0 :=
    AvramDividend.Classical.avram_p4_f4_positive_clock_centered_integral_of_zero_complement
      S hS M hMzero hZeroOutside
  have hUpperS : ∀ᵐ ω ∂(P.restrict S), F ω ≤ B + M ω :=
    ae_restrict_of_ae hUpper
  have hConstI : Integrable (fun _ : Ω => B) P := integrable_const _
  have hAddI : Integrable (fun ω => B + M ω) P := hConstI.add hMI
  have hBound : (∫ ω in S, F ω ∂P) ≤ (∫ ω in S, B + M ω ∂P) :=
    integral_mono_ae hFI.restrict hAddI.restrict hUpperS
  calc
    (∫ ω in S, F ω ∂P) ≤ (∫ ω in S, B + M ω ∂P) := hBound
    _ = (∫ ω in S, B ∂P) + (∫ ω in S, M ω ∂P) :=
      integral_add hConstI.restrict hMI.restrict
    _ = (∫ ω in S, B ∂P) := by rw [hZeroS, add_zero]
