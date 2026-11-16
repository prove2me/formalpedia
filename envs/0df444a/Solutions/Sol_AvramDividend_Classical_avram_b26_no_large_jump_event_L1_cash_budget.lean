-- Prove2me | solution 1 for AvramDividend.Classical.avram_b26_no_large_jump_event_L1_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:58:32.34879+00:00
-- url     : https://prove2.me/submissions/f5cb470b-c1ec-47a5-801d-01ddb8c68091

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b26_L1_vanishing_error_preserves_integral_budget
import Theorems.Thm_AvramDividend_Classical_avram_b26_L1_vanishing_under_measure_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (F W : Ω → ℝ) (G E : ℕ → Ω → ℝ)
    (hFI : Integrable F (P.restrict A))
    (hWI : Integrable W (P.restrict A))
    (hGI : ∀ n, Integrable (G n) (P.restrict A))
    (hEI : ∀ n, Integrable (E n) P)
    (hGmean : ∀ n, (∫ ω, G n ω ∂(P.restrict A)) = 0)
    (hEglobal : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂P) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ W ω + G n ω + E n ω) :
    (∫ ω, F ω ∂(P.restrict A)) ≤
      (∫ ω, W ω ∂(P.restrict A)) := by
  have hdom : P.restrict A ≤ P := Measure.restrict_le_self
  have hErestricted (n : ℕ) : Integrable (E n) (P.restrict A) :=
    (hEI n).mono_measure hdom
  have hEsmall :=
    avram_b26_L1_vanishing_under_measure_domination
      (P.restrict A) P hdom E hEI hEglobal
  exact avram_b26_L1_vanishing_error_preserves_integral_budget
    (P.restrict A) F W G E
    hFI hWI hGI hErestricted hGmean hEsmall hCash
