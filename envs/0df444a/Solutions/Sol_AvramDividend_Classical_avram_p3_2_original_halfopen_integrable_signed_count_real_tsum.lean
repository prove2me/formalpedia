-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_halfopen_integrable_signed_count_real_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:32:25.730453+00:00
-- url     : https://prove2.me/submissions/ab294eaf-b418-480a-b1cd-dc27d462fb91

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Integrable real signed original Lévy jump count on a genuine physical
half-open interval, expressed using its source-exact positive/negative sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let Nst : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        ({u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} ∩
          Set.Ioc s t)).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Integrable F Nst →
      (∫ p, F p ∂Nst) =
        (∑' u : ℝ≥0,
          if (0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
            u ∈ Set.Ioc s t then
            ENNReal.ofReal (F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal -
        (∑' u : ℝ≥0,
          if (0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
            u ∈ Set.Ioc s t then
            ENNReal.ofReal (-F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal := by
  dsimp
  intro hInt
  have hSigned :=
    avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
      X ω s t F hF
  dsimp at hSigned ⊢
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt]
  rw [hSigned.1, hSigned.2]
