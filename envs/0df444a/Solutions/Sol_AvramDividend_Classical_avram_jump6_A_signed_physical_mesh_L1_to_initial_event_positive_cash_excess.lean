-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_signed_physical_mesh_L1_to_initial_event_positive_cash_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:47:43.092733+00:00
-- url     : https://prove2.me/submissions/5795451e-787e-4b64-ad26-180acca91f01

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_eventwise_cash_positive_excess_le_actual_signed_L1_error
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (F : Ω → ℝ) (w : ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hFI : IntegrableOn F A P)
    (hGI : ∀ m, IntegrableOn (G m) A P)
    (hJI : ∀ m, IntegrableOn (J m) A P)
    (hEI : ∀ m, IntegrableOn (E m) A P)
    (hBound : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ w + G m ω + J m ω + E m ω)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∃ m, (∫ ω in A, |E m ω| ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ m, (∫ ω in A,
        max (F ω - w - G m ω - J m ω) 0 ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨m, hm⟩ := hSmall ε hε
  refine ⟨m, ?_⟩
  exact (avram_jump6_A_eventwise_cash_positive_excess_le_actual_signed_L1_error
    A F (G m) (J m) (E m) w
    hFI (hGI m) (hJI m) (hEI m) (hBound m)).trans hm