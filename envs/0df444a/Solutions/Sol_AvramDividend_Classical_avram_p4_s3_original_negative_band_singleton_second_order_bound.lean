-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_singleton_second_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:38:37.077746+00:00
-- url     : https://prove2.me/submissions/934c3fd5-cdfa-4464-ac54-e4c1fbb92bb3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
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
    r - r ^ 2 ≤ P.real {ω : Ω | K ω = 1} ∧
    P.real {ω : Ω | K ω = 1} ≤ r := by
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
  change r - r ^ 2 ≤ P.real {ω : Ω | K ω = 1} ∧
    P.real {ω : Ω | K ω = 1} ≤ r
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
  have hFirstMean := avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n
  change (∫ ω, (N ω).toReal ∂P) = r at hFirstMean
  have hMean : (∫ ω, (K ω : ℝ) ∂P) = r := by
    rw [← hfun]
    exact hFirstMean
  have hf := avram_p4_f2_original_band_count_factorial_moment_exact X T n
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hf
  have hfI : Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    rw [← hfun2]
    exact hf.1
  have hfMean : (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) = r ^ 2 := by
    rw [← hfun2]
    exact hf.2
  have hOne : MeasurableSet {ω : Ω | K ω = 1} := by
    change MeasurableSet (K ⁻¹' ({1} : Set ℕ))
    exact hm (measurableSet_singleton 1)
  have hIndicator : (fun ω : Ω => if K ω = 1 then (1 : ℝ) else 0) =
      ({ω : Ω | K ω = 1}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : K ω = 1 <;> simp [Set.indicator, h]
  have hIfI : Integrable (fun ω : Ω => if K ω = 1 then (1 : ℝ) else 0) P := by
    rw [hIndicator]
    exact (integrable_const (1 : ℝ)).indicator hOne
  have hIfMean : (∫ ω, (if K ω = 1 then (1 : ℝ) else 0) ∂P) =
      P.real {ω : Ω | K ω = 1} := by
    rw [hIndicator]
    exact integral_indicator_one hOne
  have hLowerPoint (ω : Ω) :
      (K ω : ℝ) - (K ω : ℝ) * ((K ω : ℝ) - 1) ≤
        (if K ω = 1 then (1 : ℝ) else 0) := by
    by_cases h1 : K ω = 1
    · simp [h1]
    · by_cases h0 : K ω = 0
      · simp [h0]
      · have htwo : (2 : ℝ) ≤ (K ω : ℝ) := by
          have hnat : 2 ≤ K ω := by omega
          exact_mod_cast hnat
        have hzero : (0 : ℝ) ≤ (K ω : ℝ) := by positivity
        simp only [if_neg h1]
        nlinarith [mul_nonneg hzero (sub_nonneg.mpr htwo)]
  have hUpperPoint (ω : Ω) :
      (if K ω = 1 then (1 : ℝ) else 0) ≤ (K ω : ℝ) := by
    by_cases h : K ω = 1
    · simp [h]
    · simp [h]
  have hL := integral_mono_ae (hFirst.sub hfI) hIfI
    (Filter.Eventually.of_forall hLowerPoint)
  have hU := integral_mono_ae hIfI hFirst
    (Filter.Eventually.of_forall hUpperPoint)
  simp only [Pi.sub_apply] at hL
  rw [integral_sub hFirst hfI, hMean, hfMean, hIfMean] at hL
  rw [hIfMean, hMean] at hU
  exact ⟨hL, hU⟩
