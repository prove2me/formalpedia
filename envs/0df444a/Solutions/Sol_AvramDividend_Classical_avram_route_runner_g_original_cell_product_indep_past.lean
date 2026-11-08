-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_g_original_cell_product_indep_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:36:01.666584+00:00
-- url     : https://prove2.me/submissions/a7f3e5cd-503e-4684-a1de-096c5b68d5e5

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_arbitrary_shift_marked_loss
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    IndepFun H (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) P := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := t - s
  let Z : Ω → (ℝ≥0 → ℝ) :=
    fun ω v => X.X (s + v) ω - X.X s ω
  obtain ⟨F, hF, _, hRep⟩ :=
    avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon T k
  have hIndep : IndepFun H (fun ω => F (Z ω)) P := by
    exact levy_future_path_measurable_jump_extractor_indep_past_ws01b
      X s H hH F hF
  have hEq (ω : Ω) :
      (∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
      F (Z ω) := by
    obtain ⟨hRC, hLL⟩ :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
    have hf := hRep (Z ω) hRC hLL
    have hl := avram_route_runner_e_arbitrary_shift_marked_loss X ω s T k
    rw [hl] at hf
    have hst' : s + T = t := by
      dsimp only [T]
      exact add_tsub_cancel_of_le hst
    rw [hst'] at hf
    have hp :=
      avram_route_runner_f_original_unit_grid_cell_product_laplace X ω s t ht k
    exact hp.trans hf.symm
  have hFun : (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
      (fun ω => F (Z ω)) := funext hEq
  rw [hFun]
  exact hIndep
