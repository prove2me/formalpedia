-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f2_original_negative_band_nonvoid_second_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:21:25.741074+00:00
-- url     : https://prove2.me/submissions/c83a7986-a696-4429-a19c-2d9f8e2e9def

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_void_probability_factorial_integral_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-band jump occurrence differs from its mean by at most half its factorial moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    r - r ^ 2 / 2 ≤ P.real {ω : Ω | K ω ≠ 0} ∧
    P.real {ω : Ω | K ω ≠ 0} ≤ r := by
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change r - r ^ 2 / 2 ≤ P.real {ω : Ω | K ω ≠ 0} ∧
    P.real {ω : Ω | K ω ≠ 0} ≤ r
  have hm : Measurable K :=
    avram_p4_f2_original_negative_band_ncard_measurable X T n
  have hreal (ω : Ω) : (N ω).toReal = (K ω : ℝ) := by
    have hN : N ω = (K ω : ℝ≥0∞) :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
    rw [hN, ENNReal.toReal_natCast]
  have hfun : (fun ω => (N ω).toReal) = (fun ω => (K ω : ℝ)) :=
    funext hreal
  have hfun2 : (fun ω => (N ω).toReal * ((N ω).toReal - 1)) =
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) := by
    funext ω
    rw [hreal ω]
  have hFirst := avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  change Integrable (fun ω => (N ω).toReal) P at hFirst
  rw [hfun] at hFirst
  have hFactorial := (avram_p4_f2_original_band_count_factorial_moment_exact X T n)
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hFactorial
  have hSecondMean : (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) =
      r ^ 2 := by
    rw [← hfun2]
    exact hFactorial.2
  have hSecond : Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    rw [← hfun2]
    exact hFactorial.1
  have hFirstMean := avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n
  change (∫ ω, (N ω).toReal ∂P) = r at hFirstMean
  have hMean : (∫ ω, (K ω : ℝ) ∂P) = r := by
    rw [← hfun]
    exact hFirstMean
  obtain ⟨hlo, hhi⟩ :=
    avram_p4_f2_void_probability_factorial_integral_sandwich P K hm hFirst hSecond
  rw [hMean, hSecondMean] at hlo
  rw [hMean] at hhi
  exact ⟨hlo, hhi⟩
