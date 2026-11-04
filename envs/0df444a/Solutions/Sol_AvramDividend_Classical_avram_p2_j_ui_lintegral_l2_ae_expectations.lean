-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_lintegral_l2_ae_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:18:13.047587+00:00
-- url     : https://prove2.me/submissions/8a8c65ad-732c-4ba9-87f5-d0aa8fc75f77

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Squared ENNReal lintegral envelopes yield convergence of genuine expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, (∫⁻ ω, ‖Y n ω‖ₑ ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have hLp : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal) := by
    intro n
    exact avram_p2_j_ui_lintegral_squared_enorm_bound P (Y n) B (hB n)
  exact avram_p2_j_ui_l2_ae_expectations_direct P Y Z B hm hLp hae
