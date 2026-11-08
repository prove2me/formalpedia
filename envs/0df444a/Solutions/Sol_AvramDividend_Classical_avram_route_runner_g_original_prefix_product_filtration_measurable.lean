-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_g_original_prefix_product_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:21:02.869242+00:00
-- url     : https://prove2.me/submissions/178b35c8-3ec4-49f4-ad02-c7e3e3038133

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_original_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k : ℕ) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset,
        Real.exp (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by 
  classical
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let H : Ω → ℝ := fun ω =>
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))
  have hH : Measurable[𝓕 T] H := by
    exact avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable X T k
  have hEq (ω : Ω) :
      (∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
      H ω := by
    have hS : (S ω).filter (fun u => (0 : ℝ≥0) < u) = S ω := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · exact fun hu => hu.1
      · intro hu
        have hp := (avram_redux19_original_strict_negative_marked_times_finite
          X ω T k).mem_toFinset.mp hu
        exact ⟨hu, hp.1⟩
    have hp := avram_route_runner_e_original_cell_product_laplace X ω 0 T k
    rw [hS] at hp
    simpa only [H, S] using hp.symm
  have hFun : (fun ω : Ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) = H :=
    funext hEq
  change Measurable[𝓕 T] (fun ω : Ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  rw [hFun]
  exact hH
