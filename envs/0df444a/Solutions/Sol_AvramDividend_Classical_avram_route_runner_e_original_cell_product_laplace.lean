-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_e_original_cell_product_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:50:59.058713+00:00
-- url     : https://prove2.me/submissions/1f22d19c-e962-4d84-b63d-f81f600071dc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_cell_weighted_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux19_finite_nonnegative_marked_sum_real_exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω t k).toFinset.filter
        (fun u => s < u)
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
      ∏ u ∈ S, Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
  dsimp only
  let S : Finset ℝ≥0 :=
    (avram_redux19_original_strict_negative_marked_times_finite X ω t k).toFinset.filter
      (fun u => s < u)
  have hsum := avram_bv_jump8_turn14_original_cell_weighted_finite_sum
    X ω s t k (fun x : ℝ => ENNReal.ofReal (-x)) (by fun_prop)
  change Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 < -(1 / ((k : ℝ) + 1))
    then ENNReal.ofReal (-p.2) else 0
    ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
    ∏ u ∈ S, Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  rw [hsum]
  have hneg : ∀ u ∈ S,
      0 ≤ -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).1
    have hsource := (avram_redux19_original_strict_negative_marked_times_finite X ω t k).mem_toFinset.mp hu'
    have hden : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith [hsource.2.2]
  have hexp := avram_redux19_finite_nonnegative_marked_sum_real_exponential
    S (fun u => -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) hneg
  rw [hexp]
  simp only [neg_neg]
  rw [Real.exp_sum]
