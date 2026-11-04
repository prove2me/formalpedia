-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_real_second_moment_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:56:23.885143+00:00
-- url     : https://prove2.me/submissions/a3fe7100-3776-4268-ab89-304af2ba4e83

import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_tail_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! Real-valued L² gives explicit tail control without prior L¹ integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (R : ℝ≥0) (hR : 0 < R) (K : ENNReal)
    (hK : (∫⁻ ω, ‖Y ω‖ₑ ^ (2 : ℕ) ∂P) ≤ K) :
    (R : ENNReal) * (∫⁻ ω,
      (if (R : ENNReal) ≤ ‖Y ω‖ₑ then ‖Y ω‖ₑ else 0) ∂P) ≤ K := by
  exact avram_p2_j_ui_quantitative_l2_tail_lintegral
    P (fun ω => ‖Y ω‖ₑ) hY.enorm R hR K hK
