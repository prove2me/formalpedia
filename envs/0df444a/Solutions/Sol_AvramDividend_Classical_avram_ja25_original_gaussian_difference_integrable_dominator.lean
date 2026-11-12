-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja25_original_gaussian_difference_integrable_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:39:13.728508+00:00
-- url     : https://prove2.me/submissions/62cc6a9e-fb67-42f2-ad94-4f58fe129a22

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- All original Gaussian finite-cutoff differences have the same L2 count envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (n : ℕ) (t : ℝ≥0) :
    ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        ‖(avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) ^ 2‖ ≤ G ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let F : ℕ → Ω → ℝ := fun k ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  let r : ℝ := ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  let G : Ω → ℝ := fun ω => 2 * ((N ω).toReal ^ 2 + r ^ 2)
  have hN2 : Integrable (fun ω => (N ω).toReal ^ 2) P := by
    simpa only [N] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2 X hFinite t).1
  have hG : Integrable G P :=
    (hN2.add (integrable_const _)).const_mul 2
  have hNfinite : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards [avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
      X hFinite] with ω hω
    simpa only [N] using hω t
  refine ⟨G, hG, ?_⟩
  intro k
  filter_upwards [hNfinite] with ω hω
  have hS0 : 0 ≤ (N ω).toReal + r :=
    add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hPart (a b : ℕ) (hab : a ≤ b) :
      |F b ω - F a ω| ≤ (N ω).toReal + r := by
    have hRaw := avram_anoise19_original_gaussian_residual_cutoff_count_bound
      X hFinite a b hab t ω hω
    have hCoeff : (1 / ((a : ℝ) + 1) : ℝ) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      simp
    have hProd : (1 / ((a : ℝ) + 1)) * ((N ω).toReal + r) ≤
        (N ω).toReal + r := by
      have hx := mul_nonneg (sub_nonneg.mpr hCoeff) hS0
      nlinarith
    exact le_trans (by simpa only [F, N, r] using hRaw) hProd
  have hPath : |F n ω - F k ω| ≤ (N ω).toReal + r := by
    rcases le_total n k with hnk | hkn
    · simpa only [abs_sub_comm] using hPart n k hnk
    · exact hPart k n hkn
  have hSq : (F n ω - F k ω) ^ 2 ≤ ((N ω).toReal + r) ^ 2 :=
    (sq_le_sq).mpr (by
      simpa [abs_of_nonneg hS0] using hPath)
  have hTwo : ((N ω).toReal + r) ^ 2 ≤
      2 * ((N ω).toReal ^ 2 + r ^ 2) := by
    nlinarith [sq_nonneg ((N ω).toReal - r)]
  have h0 : 0 ≤ (F n ω - F k ω) ^ 2 := sq_nonneg _
  change ‖(F n ω - F k ω) ^ 2‖ ≤ 2 * ((N ω).toReal ^ 2 + r ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact le_trans hSq hTwo