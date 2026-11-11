-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise21_original_gaussian_residual_L2_cutoff_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:42:10.365094+00:00
-- url     : https://prove2.me/submissions/05bf07cf-637e-4815-8820-c717ecc058f1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise20_original_gaussian_residual_limit_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Physical Gaussian residual error has quantitative L² rate with no large-mark moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hRsource : ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
      atTop (nhds (R T ω)))
    (hRmeas : AEStronglyMeasurable (R T) P)
    (hCutMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) P) :
    ∀ n : ℕ,
      Integrable (fun ω =>
        (R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2) P ∧
      (∫ ω, (R T ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2 ∂P) ≤
        2 * (1 / ((n : ℝ) + 1)) ^ 2 *
          (2 * (((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) ^ 2 +
            ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  have hMoment :
      Integrable (fun ω => (N ω).toReal ^ 2) P ∧
        (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ r ^ 2 + r := by
    simpa only [N, r] using
      avram_anoise18_original_total_negative_count_finite_activity_L2
        X hFinite T
  have hFiniteCount : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards [
      avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
        X hFinite] with ω hω
    simpa only [N] using hω T
  intro n
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  let f : Ω → ℝ := fun ω =>
    (R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2
  let g : Ω → ℝ := fun ω =>
    2 * ε ^ 2 * ((N ω).toReal ^ 2 + r ^ 2)
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hMeasF : AEStronglyMeasurable f P := by
    exact (hRmeas.sub (hCutMeas n)).pow 2
  have hMeasG : Integrable g P := by
    have hSum : Integrable (fun ω => (N ω).toReal ^ 2 + r ^ 2) P :=
      hMoment.1.add (integrable_const _)
    exact hSum.const_mul (2 * ε ^ 2)
  have hBound : ∀ᵐ ω ∂P, f ω ≤ g ω := by
    filter_upwards [hRsource, hFiniteCount] with ω hSource hNfinite
    have hAbs :
        |R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
          ε * ((N ω).toReal + r) := by
      simpa only [N, r, ε] using
        avram_anoise20_original_gaussian_residual_limit_count_bound
          X hFinite R n T ω hSource hNfinite
    have hN0 : 0 ≤ (N ω).toReal := ENNReal.toReal_nonneg
    have hSum0 : 0 ≤ ε * ((N ω).toReal + r) :=
      mul_nonneg hε0 (add_nonneg hN0 hr0)
    have hSq :
        (R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2 ≤
        (ε * ((N ω).toReal + r)) ^ 2 :=
      (sq_le_sq).mpr (by simpa [abs_of_nonneg hSum0] using hAbs)
    have hTwo :
        ((N ω).toReal + r) ^ 2 ≤
          2 * ((N ω).toReal ^ 2 + r ^ 2) := by
      nlinarith [sq_nonneg ((N ω).toReal - r)]
    change (R T ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2 ≤
      2 * ε ^ 2 * ((N ω).toReal ^ 2 + r ^ 2)
    calc
      _ ≤ (ε * ((N ω).toReal + r)) ^ 2 := hSq
      _ = ε ^ 2 * ((N ω).toReal + r) ^ 2 := by ring
      _ ≤ ε ^ 2 * (2 * ((N ω).toReal ^ 2 + r ^ 2)) :=
        mul_le_mul_of_nonneg_left hTwo (sq_nonneg ε)
      _ = 2 * ε ^ 2 * ((N ω).toReal ^ 2 + r ^ 2) := by ring
  have hFint : Integrable f P := by
    apply hMeasG.mono hMeasF
    filter_upwards [hBound] with ω hω
    have hf0 : 0 ≤ f ω := by dsimp [f]; positivity
    have hg0 : 0 ≤ g ω := by
      dsimp [g]
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg hg0] using hω
  have hIntegral : (∫ ω, f ω ∂P) ≤ ∫ ω, g ω ∂P :=
    integral_mono_ae hFint hMeasG hBound
  have hIntegralG :
      (∫ ω, g ω ∂P) =
        2 * ε ^ 2 * ((∫ ω, (N ω).toReal ^ 2 ∂P) + r ^ 2) := by
    dsimp [g]
    rw [integral_const_mul, integral_add hMoment.1 (integrable_const _)]
    simp
  constructor
  · simpa only [f] using hFint
  · change (∫ ω, f ω ∂P) ≤ 2 * ε ^ 2 * (2 * r ^ 2 + r)
    calc
      (∫ ω, f ω ∂P) ≤ ∫ ω, g ω ∂P := hIntegral
      _ = 2 * ε ^ 2 * ((∫ ω, (N ω).toReal ^ 2 ∂P) + r ^ 2) := hIntegralG
      _ ≤ 2 * ε ^ 2 * ((r ^ 2 + r) + r ^ 2) := by
        have hBase :
            (∫ ω, (N ω).toReal ^ 2 ∂P) + r ^ 2 ≤
              (r ^ 2 + r) + r ^ 2 := by linarith [hMoment.2]
        exact mul_le_mul_of_nonneg_left hBase (by positivity)
      _ = 2 * ε ^ 2 * (2 * r ^ 2 + r) := by ring