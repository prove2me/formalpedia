-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise24_original_cutoff_square_expectations_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:15:03.362284+00:00
-- url     : https://prove2.me/submissions/f2266fe0-c83d-40be-a952-a395a7e1e820

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
set_option pp.fullNames true
set_option pp.universes true

set_option pp.explicit true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Physical count dominance yields convergence of original residual square energies. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hRsource : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω) atTop (nhds (R T ω)))
    (hCutMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) P)
    (hCutSquare : Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P) :
    Tendsto (fun n : ℕ => ∫ ω,
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2 ∂P)
      atTop (nhds (∫ ω, (R T ω) ^ 2 ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ Iio (0 : ℝ))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  let F : ℕ → Ω → ℝ := fun n ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω
  let g : Ω → ℝ := fun ω => 3 * ((F 0 ω) ^ 2 + (N ω).toReal ^ 2 + r ^ 2)
  have hN2 : Integrable (fun ω => (N ω).toReal ^ 2) P := by
    simpa only [N] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2 X hFinite T).1
  have hNfinite : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards [avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
      X hFinite] with ω hω
    simpa only [N] using hω T
  have hF0 : Integrable (fun ω => (F 0 ω) ^ 2) P := by
    simpa only [F] using hCutSquare
  have hG : Integrable g P := by
    have hSum : Integrable (fun ω =>
        (F 0 ω) ^ 2 + (N ω).toReal ^ 2 + r ^ 2) P :=
      (hF0.add hN2).add (integrable_const _)
    exact hSum.const_mul 3
  have hMeas (n : ℕ) : AEStronglyMeasurable (fun ω => (F n ω) ^ 2) P :=
    (hCutMeas n).pow 2
  have hBound (n : ℕ) : ∀ᵐ ω ∂P, ‖(F n ω) ^ 2‖ ≤ g ω := by
    filter_upwards [hNfinite] with ω hω
    have hPath : |F n ω - F 0 ω| ≤ (N ω).toReal + r := by
      simpa [F, N, r] using
        (avram_anoise19_original_gaussian_residual_cutoff_count_bound
          X hFinite 0 n (Nat.zero_le n) T ω hω)
    have hTri : |F n ω| ≤ (N ω).toReal + r + |F 0 ω| := by
      calc
        |F n ω| = |(F n ω - F 0 ω) + F 0 ω| := by ring
        _ ≤ |F n ω - F 0 ω| + |F 0 ω| := abs_add_le _ _
        _ ≤ (N ω).toReal + r + |F 0 ω| := by linarith [hPath]
    have hSum0 : 0 ≤ (N ω).toReal + r + |F 0 ω| := by positivity
    have hSq : (F n ω) ^ 2 ≤ ((N ω).toReal + r + |F 0 ω|) ^ 2 :=
      (sq_le_sq).mpr (by simpa [abs_of_nonneg hSum0] using hTri)
    have hThree : ((N ω).toReal + r + |F 0 ω|) ^ 2 ≤
        3 * ((F 0 ω) ^ 2 + (N ω).toReal ^ 2 + r ^ 2) := by
      have hInner : ((N ω).toReal + r + |F 0 ω|) ^ 2 ≤
          3 * ((|F 0 ω|) ^ 2 + (N ω).toReal ^ 2 + r ^ 2) := by
        nlinarith [sq_nonneg (|F 0 ω| - (N ω).toReal),
          sq_nonneg (|F 0 ω| - r), sq_nonneg ((N ω).toReal - r)]
      simpa only [sq_abs] using hInner
    have h0 : 0 ≤ (F n ω) ^ 2 := sq_nonneg _
    change ‖(F n ω) ^ 2‖ ≤ 3 * ((F 0 ω) ^ 2 + (N ω).toReal ^ 2 + r ^ 2)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using le_trans hSq hThree
  have hLimit : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (F n ω) ^ 2)
      atTop (nhds ((R T ω) ^ 2)) := by
    filter_upwards [hRsource] with ω hω
    exact hω.pow 2
  change Tendsto (fun n : ℕ => ∫ ω, (F n ω) ^ 2 ∂P)
    atTop (nhds (∫ ω, (R T ω) ^ 2 ∂P))
  exact tendsto_integral_of_dominated_convergence g hMeas hG hBound hLimit