-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord8_t10_equalcell_marked_product_stationary_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:01:14.494206+00:00
-- url     : https://prove2.me/submissions/bd6609cd-7005-4634-a8e0-41ce602c1c23

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_original_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_arbitrary_shift_marked_loss
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let J : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
      ∏ u ∈ (J ω).filter (fun u =>
        (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ i : Fin (n + 1),
      (∫ ω, C i ω ∂P) =
        (∫ ω, ∏ u ∈ S ω,
          Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let J : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∏ u ∈ (J ω).filter (fun u =>
      (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  change ∀ i : Fin (n + 1),
    (∫ ω, C i ω ∂P) =
      (∫ ω, ∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P)
  intro i
  let s : ℝ≥0 := (i.val : ℝ≥0) * T
  let t : ℝ≥0 := ((i.val : ℝ≥0) + 1) * T
  have hst : s + T = t := by simp only [s, t, add_mul, one_mul]
  have hn0 : 0 < (n : ℝ≥0) + 1 := by positivity
  have hi : (i.val : ℝ≥0) + 1 ≤ (n : ℝ≥0) + 1 := by
    have hiNat : i.val + 1 ≤ n + 1 := by omega
    exact_mod_cast hiNat
  have ht : t ≤ 1 := by
    have hh : ((i.val : ℝ≥0) + 1) / ((n : ℝ≥0) + 1) ≤ 1 := by
      apply (div_le_iff₀ hn0).2
      simpa using hi
    simpa only [t, T, div_eq_mul_inv, one_mul] using hh
  let path0 : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let pathS : Ω → (ℝ≥0 → ℝ) := fun ω v => X.X (s + v) ω - X.X s ω
  obtain ⟨F, hF, _hBounds, hFpath⟩ :=
    avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon T k
  have h0 : Measurable path0 := by
    convert (avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
      X (0 : ℝ≥0)) using 1
    funext ω v
    simp [path0, X.X_zero]
  have hS : Measurable pathS := by
    exact avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X s
  have hLaw : Measure.map pathS P = Measure.map path0 P := by
    exact levy_shiftedFuturePath_stationary_law X s
  have hTransfer :
      (∫ ω, F (pathS ω) ∂P) = ∫ ω, F (path0 ω) ∂P := by
    calc
      (∫ ω, F (pathS ω) ∂P) =
          ∫ f, F f ∂(Measure.map pathS P) :=
        (integral_map hS.aemeasurable hF.aestronglyMeasurable).symm
      _ = ∫ f, F f ∂(Measure.map path0 P) := by rw [hLaw]
      _ = ∫ ω, F (path0 ω) ∂P :=
        integral_map h0.aemeasurable hF.aestronglyMeasurable
  have hCell : ∀ ω : Ω, C i ω = F (pathS ω) := by
    intro ω
    obtain ⟨hRC, hLL⟩ :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
    have hFShift := hFpath (pathS ω) hRC hLL
    have hShift := avram_route_runner_e_arbitrary_shift_marked_loss X ω s T k
    have hProd :=
      avram_route_runner_f_original_unit_grid_cell_product_laplace X ω s t ht k
    rw [hFShift, hShift, hst]
    simpa only [C, J, s, t, pathS] using hProd
  have hOrigin : ∀ ω : Ω,
      (∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
        F (path0 ω) := by
    intro ω
    have hPos : (S ω).filter (fun u => (0 : ℝ≥0) < u) = S ω := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · exact fun hu => hu.1
      · intro hu
        have hu' := (avram_redux19_original_strict_negative_marked_times_finite
          X ω T k).mem_toFinset.mp hu
        exact ⟨hu, hu'.1⟩
    have hE := avram_route_runner_e_original_cell_product_laplace
      X ω (0 : ℝ≥0) T k
    rw [hPos] at hE
    have hF0 := hFpath (path0 ω) (X.rightCont ω) (X.leftLim ω)
    rw [hF0]
    simpa only [S, path0, zero_lt_iff] using hE.symm
  calc
    (∫ ω, C i ω ∂P) = ∫ ω, F (pathS ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hCell ω
    _ = ∫ ω, F (path0 ω) ∂P := hTransfer
    _ = (∫ ω, ∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (hOrigin ω).symm
