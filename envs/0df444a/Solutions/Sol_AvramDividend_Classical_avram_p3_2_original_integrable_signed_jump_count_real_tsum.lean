-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_integrable_signed_jump_count_real_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:32:30.024458+00:00
-- url     : https://prove2.me/submissions/43f71a3a-5549-44d4-bfec-f32c2afb39ee

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original signed Lévy jump integral is exactly the difference
between its positive and negative original jump-count sums under L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Integrable F NX →
      (∫ p, F p ∂NX) =
        (∑' u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
            ENNReal.ofReal (F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal -
        (∑' u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
            ENNReal.ofReal (-F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal := by
  dsimp
  intro hInt
  have hSigned :=
    avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum X ω F hF
  dsimp at hSigned ⊢
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt]
  rw [hSigned.1, hSigned.2]
