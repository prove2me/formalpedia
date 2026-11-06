-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:58:32.045201+00:00
-- url     : https://prove2.me/submissions/05ae985d-950b-453d-8430-737302bd2129

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact positive and negative original signed-kernel integrals as actual
time-indexed original Lévy jump sums. -/
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
  have hPair : Measurable (fun u : ℝ≥0 => (u, ω)) :=
    measurable_id.prodMk measurable_const
  have hSection : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hPair
  have hMark : Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    measurable_id.prodMk hSection
  have hSet :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
      X ω hMark
  dsimp
  constructor
  · simpa only [Set.mem_setOf_eq] using
      (avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
        _ hSet _ hMark (fun p => ENNReal.ofReal (F p))
        (ENNReal.measurable_ofReal.comp hF))
  · simpa only [Set.mem_setOf_eq] using
      (avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
        _ hSet _ hMark (fun p => ENNReal.ofReal (-F p))
        (ENNReal.measurable_ofReal.comp hF.neg))
