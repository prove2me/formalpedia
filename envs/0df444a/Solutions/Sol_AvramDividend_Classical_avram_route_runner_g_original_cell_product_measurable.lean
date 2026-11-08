-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_g_original_cell_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:14:07.914836+00:00
-- url     : https://prove2.me/submissions/99832525-adee-4f1f-8065-1144969dddc3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_arbitrary_shift_marked_loss
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ) :
    Measurable (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by  
  classical
  let T : ℝ≥0 := t - s
  let pathS : Ω → (ℝ≥0 → ℝ) :=
    fun ω v => X.X (s + v) ω - X.X s ω
  obtain ⟨F, hF, _, hRep⟩ :=
    avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon T k
  have hpath : Measurable pathS := by
    exact avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X s
  have hpoint (ω : Ω) :
      (∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
          X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
      F (pathS ω) := by
    obtain ⟨hRC, hLL⟩ :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
    have hf := hRep (pathS ω) hRC hLL
    have hl := avram_route_runner_e_arbitrary_shift_marked_loss X ω s T k
    rw [hl] at hf
    have hst' : s + T = t := by
      dsimp only [T]
      exact add_tsub_cancel_of_le hst
    rw [hst'] at hf
    have hp :=
      avram_route_runner_f_original_unit_grid_cell_product_laplace X ω s t ht k
    exact hp.trans hf.symm
  convert hF.comp hpath using 1
  funext ω
  exact hpoint ω
