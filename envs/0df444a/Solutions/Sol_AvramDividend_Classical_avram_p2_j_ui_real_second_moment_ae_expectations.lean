-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_real_second_moment_ae_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:26:15.682171+00:00
-- url     : https://prove2.me/submissions/ed70ccab-8d4d-4629-a059-88c2a14f1e80

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_second_moment_to_l2_norm
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Real squared-moment estimates feed the Bochner Vitali limit theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hInt : ∀ n, Integrable (fun ω => ‖Y n ω‖ ^ 2) P)
    (hB : ∀ n, (∫ ω, ‖Y n ω‖ ^ 2 ∂P) ≤ (B : ℝ) ^ 2)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have hL2 : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal) := by
    intro n
    exact avram_p2_j_ui_second_moment_to_l2_norm
      P (Y n) B (hm n) (hInt n) (hB n)
  exact avram_p2_j_ui_l2_ae_expectations_direct P Y Z B hm hL2 hae
