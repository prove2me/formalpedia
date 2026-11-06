-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_second_moment_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:13:05.94045+00:00
-- url     : https://prove2.me/submissions/8820dedf-fc06-4c91-9b6f-415b9bb66303

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
    Integrable (fun ω => if 2 ≤ K ω then ((K ω : ℝ) ^ 2) else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then ((K ω : ℝ) ^ 2) else 0) ∂P) ≤ 2 * r ^ 2 := by
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
  let Q : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0
  change Integrable Q P ∧ (∫ ω, Q ω ∂P) ≤ 2 * r ^ 2
  have hm : Measurable K :=
    avram_p4_f2_original_negative_band_ncard_measurable X T n
  have hReal (ω : Ω) : (N ω).toReal = (K ω : ℝ) := by
    have hN : N ω = (K ω : ℝ≥0∞) :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
    rw [hN, ENNReal.toReal_natCast]
  have hFirst := avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  change Integrable (fun ω => (N ω).toReal) P at hFirst
  have hKFirst : Integrable (fun ω => (K ω : ℝ)) P := by
    have hfun : (fun ω => (N ω).toReal) = (fun ω => (K ω : ℝ)) :=
      funext hReal
    rw [hfun] at hFirst
    exact hFirst
  have hf := avram_p4_f2_original_band_count_factorial_moment_exact X T n
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hf
  have hfun2 : (fun ω => (N ω).toReal * ((N ω).toReal - 1)) =
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) := by
    funext ω
    rw [hReal ω]
  have hFInt : Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    rw [← hfun2]
    exact hf.1
  have hFMean : (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) = r ^ 2 := by
    rw [← hfun2]
    exact hf.2
  have hSquareInt : Integrable (fun ω => (K ω : ℝ) ^ 2) P := by
    have heq : (fun ω => (K ω : ℝ) ^ 2) =
        (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1) + (K ω : ℝ)) := by
      funext ω
      ring
    rw [heq]
    exact hFInt.add hKFirst
  have hEvent : MeasurableSet {ω : Ω | 2 ≤ K ω} := by
    change MeasurableSet (K ⁻¹' (Ici (2 : ℕ)))
    exact hm measurableSet_Ici
  have hindicator : Q = ({ω : Ω | 2 ≤ K ω}).indicator
      (fun ω => (K ω : ℝ) ^ 2) := by
    funext ω
    by_cases h : 2 ≤ K ω <;> simp [Q, Set.indicator, h]
  have hQInt : Integrable Q P := by
    rw [hindicator]
    exact hSquareInt.indicator hEvent
  refine ⟨hQInt, ?_⟩
  have hPoint (ω : Ω) :
      Q ω ≤ 2 * ((K ω : ℝ) * ((K ω : ℝ) - 1)) := by
    by_cases hk : 2 ≤ K ω
    · have hk2 : (2 : ℝ) ≤ (K ω : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (K ω : ℝ) := by positivity
      simp only [Q, if_pos hk]
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk2)]
    · have hsmall : K ω = 0 ∨ K ω = 1 := by omega
      rcases hsmall with h0 | h1
      · simp [Q, h0]
      · simp [Q, h1]
  have hBound := integral_mono_ae hQInt (hFInt.const_mul 2)
    (Filter.Eventually.of_forall hPoint)
  rw [integral_const_mul 2, hFMean] at hBound
  exact hBound
