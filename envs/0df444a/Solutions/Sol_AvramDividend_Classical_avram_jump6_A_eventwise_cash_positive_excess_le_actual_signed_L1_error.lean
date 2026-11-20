-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_eventwise_cash_positive_excess_le_actual_signed_L1_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:27:25.805184+00:00
-- url     : https://prove2.me/submissions/716010c7-699a-43c9-9e16-acd9efb5bb72

import Mathlib
open MeasureTheory Set Filter
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (F G J E : Ω → ℝ) (w : ℝ)
    (hFI : IntegrableOn F A P) (hGI : IntegrableOn G A P)
    (hJI : IntegrableOn J A P) (hEI : IntegrableOn E A P)
    (hBound : ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ w + G ω + J ω + E ω) :
    (∫ ω in A, max (F ω - w - G ω - J ω) 0 ∂P) ≤
      (∫ ω in A, |E ω| ∂P) := by
  have hPosI :
      IntegrableOn (fun ω => max (F ω - w - G ω - J ω) 0) A P := by
    exact (((hFI.sub (integrable_const _).integrableOn).sub hGI).sub hJI).sup
      (integrable_const _).integrableOn
  have hAbsI : IntegrableOn (fun ω => |E ω|) A P := hEI.abs
  apply integral_mono_ae hPosI hAbsI
  filter_upwards [hBound] with ω hω
  have hdiff : F ω - w - G ω - J ω ≤ E ω := by linarith
  exact max_le (hdiff.trans (le_abs_self _)) (abs_nonneg _)