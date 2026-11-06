-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_mass_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:23:07.112655+00:00
-- url     : https://prove2.me/submissions/e61edecc-db75-4008-8550-65ab1b6dddd8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then (K ω : ℝ) else 0) ∂P) ≤ r ^ 2 := by
  classical
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
  change Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then (K ω : ℝ) else 0) ∂P) ≤ r ^ 2
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
  have hf := avram_p4_f2_original_band_count_factorial_moment_exact X T n
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hf
  have hfI : Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    rw [← hfun2]
    exact hf.1
  have hfMean : (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) = r ^ 2 := by
    rw [← hfun2]
    exact hf.2
  have hB : MeasurableSet {ω : Ω | 2 ≤ K ω} := by
    change MeasurableSet (K ⁻¹' (Ici (2 : ℕ)))
    exact hm measurableSet_Ici
  have hindicator : (fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0) =
      ({ω : Ω | 2 ≤ K ω}).indicator (fun ω => (K ω : ℝ)) := by
    funext ω
    by_cases h : 2 ≤ K ω <;> simp [Set.indicator, h]
  have hInt : Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0) P := by
    rw [hindicator]
    exact hFirst.indicator hB
  refine ⟨hInt, ?_⟩
  have hpoint (ω : Ω) :
      (if 2 ≤ K ω then (K ω : ℝ) else 0) ≤
        (K ω : ℝ) * ((K ω : ℝ) - 1) := by
    by_cases h : 2 ≤ K ω
    · simp only [if_pos h]
      have htwo : (2 : ℝ) ≤ (K ω : ℝ) := by exact_mod_cast h
      have hzero : (0 : ℝ) ≤ (K ω : ℝ) := by positivity
      nlinarith [mul_nonneg hzero (sub_nonneg.mpr htwo)]
    · have hsmall : K ω = 0 ∨ K ω = 1 := by omega
      rcases hsmall with h0 | h1
      · simp [h0]
      · simp [h1]
  have hbound := integral_mono_ae hInt hfI
    (Filter.Eventually.of_forall hpoint)
  rw [hfMean] at hbound
  exact hbound
