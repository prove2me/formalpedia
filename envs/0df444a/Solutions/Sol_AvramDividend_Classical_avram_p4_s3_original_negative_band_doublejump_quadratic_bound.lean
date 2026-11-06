-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_doublejump_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:14:33.291549+00:00
-- url     : https://prove2.me/submissions/40db7ee5-8e16-42d4-a40b-2a5865c48b36

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-band double jumps have at most half the square of their expected count. -/
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
    P.real {ω : Ω | 2 ≤ K ω} ≤ r ^ 2 / 2 := by
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
  change P.real {ω : Ω | 2 ≤ K ω} ≤ r ^ 2 / 2
  have hKm : Measurable K :=
    avram_p4_f2_original_negative_band_ncard_measurable X T n
  have hEvent : MeasurableSet {ω : Ω | 2 ≤ K ω} := by
    change MeasurableSet (K ⁻¹' Ici (2 : ℕ))
    exact hKm measurableSet_Ici
  have hreal (ω : Ω) : (N ω).toReal = (K ω : ℝ) := by
    have hN : N ω = (K ω : ℝ≥0∞) :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
    rw [hN, ENNReal.toReal_natCast]
  have hfun :
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) =
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) := by
    funext ω
    rw [hreal ω]
  have hFact := avram_p4_f2_original_band_count_factorial_moment_exact X T n
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hFact
  have hFactI : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    rw [← hfun]
    exact hFact.1
  have hFactMean :
      (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) = r ^ 2 := by
    rw [← hfun]
    exact hFact.2
  have hpoint (k : ℕ) :
      (if 2 ≤ k then (1 : ℝ) else 0) ≤
        (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    by_cases hk : 2 ≤ k
    · simp only [if_pos hk]
      have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hprod : 0 ≤ ((k : ℝ) - 2) * ((k : ℝ) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> norm_num
  have hif :
      (fun ω : Ω => if 2 ≤ K ω then (1 : ℝ) else 0) =
      ({ω : Ω | 2 ≤ K ω}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hk : 2 ≤ K ω <;> simp [Set.indicator, hk]
  have hIfInt : Integrable
      (fun ω : Ω => if 2 ≤ K ω then (1 : ℝ) else 0) P := by
    rw [hif]
    exact (integrable_const (1 : ℝ)).indicator hEvent
  have hIfIntegral :
      (∫ ω, (if 2 ≤ K ω then (1 : ℝ) else 0) ∂P) =
        P.real {ω : Ω | 2 ≤ K ω} := by
    rw [hif]
    exact integral_indicator_one hEvent
  have hBound :=
    integral_mono_ae hIfInt (hFactI.div_const 2)
      (Filter.Eventually.of_forall (fun ω => hpoint (K ω)))
  rw [hIfIntegral, integral_div, hFactMean] at hBound
  exact hBound
