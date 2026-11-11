-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise27_original_gaussian_residual_uniform_l1_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:52:06.421194+00:00
-- url     : https://prove2.me/submissions/9120bac7-29d0-4b26-8588-46b020b9a1b7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Physical total negative mark counts dominate all intrinsic Gaussian cutoff residuals in L1. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0)
    (hCut0 : Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) P) :
    ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        ‖avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω‖ ≤ G ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ Iio (0 : ℝ))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  let F : ℕ → Ω → ℝ := fun n ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω
  let G : Ω → ℝ := fun ω => ‖F 0 ω‖ + (N ω).toReal ^ 2 + (r ^ 2 + 2)
  have hN2 : Integrable (fun ω => (N ω).toReal ^ 2) P := by
    simpa only [N] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2 X hFinite T).1
  have hG : Integrable G P := by
    have hFi : Integrable (fun ω => F 0 ω) P := by simpa only [F] using hCut0
    exact ((hFi.norm.add hN2).add (integrable_const (r ^ 2 + 2)))
  refine ⟨G, hG, ?_⟩
  have hNF : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards [avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
      X hFinite] with ω hω
    simpa only [N] using hω T
  intro n
  filter_upwards [hNF] with ω hω
  have hP : |F n ω - F 0 ω| ≤ (N ω).toReal + r := by
    simpa [F, N, r] using
      (avram_anoise19_original_gaussian_residual_cutoff_count_bound
        X hFinite 0 n (Nat.zero_le n) T ω hω)
  have hTri : |F n ω| ≤ |F 0 ω| + (N ω).toReal + r := by
    calc
      |F n ω| = |(F n ω - F 0 ω) + F 0 ω| := by ring
      _ ≤ |F n ω - F 0 ω| + |F 0 ω| := abs_add_le _ _
      _ ≤ |F 0 ω| + (N ω).toReal + r := by linarith
  have hQ : (N ω).toReal + r ≤ (N ω).toReal ^ 2 + (r ^ 2 + 2) := by
    nlinarith [sq_nonneg ((N ω).toReal - 1), sq_nonneg (r - 1)]
  change ‖F n ω‖ ≤ G ω
  simp only [Real.norm_eq_abs, G]
  linarith
