-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:56:59.883547+00:00
-- url     : https://prove2.me/submissions/2826b292-ae3f-43ed-b863-899d05003bb7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Both positive and negative nonnegative-part integrals of the actual
signed original Lévy nonlinear jump kernel equal their actual jump tsums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let NX : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ((∫⁻ p, ENNReal.ofReal (F p) ∂NX) =
       ∑' u : ℝ≥0, if 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then ENNReal.ofReal (F (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0) ∧
    ((∫⁻ p, ENNReal.ofReal (-F p) ∂NX) =
       ∑' u : ℝ≥0, if 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then ENNReal.ofReal (-F (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0) := by
  dsimp
  constructor
  · exact avram_p3_2_original_source_nonlinear_jump_count_eq_tsum
      X ω (fun p => ENNReal.ofReal (F p))
      (ENNReal.measurable_ofReal.comp hF)
  · exact avram_p3_2_original_source_nonlinear_jump_count_eq_tsum
      X ω (fun p => ENNReal.ofReal (-F p))
      (ENNReal.measurable_ofReal.comp hF.neg)
