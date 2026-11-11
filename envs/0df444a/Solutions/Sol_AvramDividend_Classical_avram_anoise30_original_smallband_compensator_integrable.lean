-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise30_original_smallband_compensator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:32:09.697759+00:00
-- url     : https://prove2.me/submissions/10d22dc0-cb4c-4de2-b4f3-93144152cbf7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original finite-intensity mark count dominates every bounded signed compensated band. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ, ∀ T : ℝ≥0,
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n T
  let R (k : ℕ) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω
  let S (ω : Ω) := avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω
  let N (ω : Ω) : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  let A : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  have hIdentity (ω : Ω) : S ω = R 0 ω - R n ω := by
    have hd := avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
      X n 0 T ω
    have hz : avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 T ω = 0 := by
      simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
    dsimp [R, S] at *
    rw [hz] at hd
    simp only [zero_sub] at hd
    linarith
  have hM (k : ℕ) : AEStronglyMeasurable (R k) P := by
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X k T).mono (𝓕.le T) le_rfl).aestronglyMeasurable
  have hS : AEStronglyMeasurable S P := by
    have hEq : S = R 0 - R n := funext hIdentity
    rw [hEq]
    exact (hM 0).sub (hM n)
  have hN2 : Integrable (fun ω => (N ω).toReal ^ 2) P :=
    (avram_anoise18_original_total_negative_count_finite_activity_L2
      X hFinite T).1
  have hD : Integrable (fun ω => (N ω).toReal ^ 2 + A + 1) P :=
    (hN2.add (integrable_const A)).add (integrable_const 1)
  have hNfin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards [avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
      X hFinite] with ω hω
    exact hω T
  have hBound : ∀ᵐ ω ∂P, ‖S ω‖ ≤ (N ω).toReal ^ 2 + A + 1 := by
    filter_upwards [hNfin] with ω hω
    have hb := avram_anoise19_original_gaussian_residual_cutoff_count_bound
      X hFinite 0 n (Nat.zero_le n) T ω hω
    have hb' : |R n ω - R 0 ω| ≤ (N ω).toReal + A := by
      simpa [R, N, A] using hb
    have heq : |S ω| = |R n ω - R 0 ω| := by
      rw [hIdentity ω, abs_sub_comm]
    have hn : 0 ≤ (N ω).toReal := ENNReal.toReal_nonneg
    have ha : 0 ≤ A := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, heq]
    nlinarith [sq_nonneg ((N ω).toReal - 1)]
  exact Integrable.mono' hD hS hBound
