-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:37:26.819196+00:00
-- url     : https://prove2.me/submissions/f98e1458-c160-46a4-b0d3-79495411736a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
/-- A real positive-clock reward budget is exactly its probability-weighted ENNReal counterpart. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (S : Set Ω) (F : Ω → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hFI : Integrable F P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMeanS : (∫ ω in S, F ω ∂P) ≤ B * (P S).toReal) :
    (∫⁻ ω in S, ENNReal.ofReal (F ω) ∂P) ≤
      ENNReal.ofReal B * P S := by
  have hRestrI : Integrable F (P.restrict S) := hFI.restrict
  have hRestrNonneg : ∀ᵐ ω ∂(P.restrict S), 0 ≤ F ω :=
    ae_restrict_of_ae hNonneg
  have hBridge :
      (∫⁻ ω in S, ENNReal.ofReal (F ω) ∂P) ≤
        ENNReal.ofReal (B * (P S).toReal) := by
    exact (AvramDividend.Classical.avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
      (P := P.restrict S) (fun _ ω => F ω) (B * (P S).toReal)
      (fun _ => hRestrI) (fun _ => hRestrNonneg) (fun _ => hMeanS)) 0
  calc
    (∫⁻ ω in S, ENNReal.ofReal (F ω) ∂P) ≤
        ENNReal.ofReal (B * (P S).toReal) := hBridge
    _ = ENNReal.ofReal B * P S := by
      rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_toReal (measure_ne_top P S)]
