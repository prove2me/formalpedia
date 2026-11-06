-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:29:18.651712+00:00
-- url     : https://prove2.me/submissions/57683a02-59b1-4098-810c-098a257a50da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every actual separated Borel cell has its intrinsic mean-zero compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal - r) P ∧
      (∫ ω, (N ω).toReal - r ∂P) = 0 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (N ω).toReal - r) P ∧
    (∫ ω, (N ω).toReal - r ∂P) = 0
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite X B hB ε hε hBsep
  have hNm : Measurable N :=
    avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X s t hst B hB
  have hRate := avram_p4_s3_original_future_negative_borel_rectangle_all_cells
    X B hB ε hε hBsep s t hst Set.univ (by simp)
  have hNRate : (∫⁻ ω, N ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa only [Measure.restrict_univ, measure_univ, one_mul] using hRate
  have hFinite : (∫⁻ ω, N ω ∂P) ≠ ⊤ := by
    rw [hNRate]
    have hTime : (t : ℝ≥0∞) - (s : ℝ≥0∞) < ⊤ :=
      lt_of_le_of_lt tsub_le_self ENNReal.coe_lt_top
    exact (ENNReal.mul_lt_top hTime hν).ne
  have hNI : Integrable (fun ω => (N ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hNm.aemeasurable hFinite
  have hMean : (∫ ω, (N ω).toReal ∂P) = r :=
    avram_p2_e_compensator_finite_nu_count_real_mean
      X s t hst B hB hν hNRate
  refine ⟨hNI.sub (integrable_const r), ?_⟩
  rw [integral_sub hNI (integrable_const r), integral_const, hMean]
  simp [Measure.real]
