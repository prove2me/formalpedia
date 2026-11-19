-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward73_initial_event_positive_residual_to_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:50:41.823584+00:00
-- url     : https://prove2.me/submissions/3b0aa151-f707-4893-8991-a0b0db8e0fd2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (G M L : Ω → ℝ) (k ε : ℝ)
    (hGI : Integrable G P) (hMI : Integrable M P)
    (hLI : Integrable L P)
    (hLzero : (∫ ω in A, L ω ∂P) = 0)
    (hResidual : (∫ ω in A, max (0 : ℝ)
      (G ω - k - (M ω + L ω)) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤
      k * (P A).toReal + (∫ ω in A, M ω ∂P) + ε := by
  have hML : Integrable (fun omega => M omega + L omega) P := hMI.add hLI
  have hBound :=
    AvramDividend.Classical.avram_pj_reward35_integrable_positive_residual_event_budget
      A G (fun omega => M omega + L omega) k ε hGI hML hResidual
  have hsum : (∫ omega in A, M omega + L omega ∂P) =
      (∫ omega in A, M omega ∂P) + (∫ omega in A, L omega ∂P) := by
    exact integral_add hMI.integrableOn hLI.integrableOn
  rw [hsum, hLzero, add_zero] at hBound
  exact hBound
