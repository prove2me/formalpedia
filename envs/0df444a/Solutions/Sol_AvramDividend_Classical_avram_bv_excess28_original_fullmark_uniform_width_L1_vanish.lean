-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess28_original_fullmark_uniform_width_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:51:04.0408+00:00
-- url     : https://prove2.me/submissions/7feac9f9-8398-45da-aa2e-22fd929c10c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original finite-activity negative jump count makes occupied-cell mesh widths vanish in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞))  := by
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  have hN : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)
      Set.univ MeasurableSet.univ
  have hMean : (∫⁻ ω, N ω ∂P) < ⊤ := by
    change (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) < ⊤
    rw [avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
      X hBV hFinite 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)]
    simpa using (ENNReal.mul_lt_top
      (by simp : ((T : ℝ≥0∞) < ⊤)) hFinite)
  have hInv : Filter.Tendsto
      (fun n : ℕ => (((n + 2 : ℕ) : ℝ≥0∞)⁻¹))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp
      (Filter.tendsto_add_atTop_nat 2)
  have hProd : Filter.Tendsto
      (fun n : ℕ => (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * (∫⁻ ω, N ω ∂P))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.Tendsto.mul_const hInv (Or.inr hMean.ne))
  change Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
    (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω ∂P)
    Filter.atTop (nhds (0 : ℝ≥0∞))
  have hEq : ∀ n : ℕ, (∫⁻ ω,
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω ∂P) =
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * (∫⁻ ω, N ω ∂P) := by
    intro n
    exact lintegral_const_mul _ hN
  simpa only [hEq] using hProd