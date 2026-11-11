-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18b_original_smallband_uniform_count_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:48:32.253653+00:00
-- url     : https://prove2.me/submissions/13d23461-c86a-4004-9174-e84ae929b0d2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every intrinsic compensated small-band cutoff is bounded by the
same physical finite negative-jump count and deterministic source rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro T
  let R (k : ℕ) (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω
  let S (k : ℕ) (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω
  let N (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  let A : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  let B : Ω → ℝ := fun ω => (N T ω).toReal ^ 2 + A + 1
  have hN2 : Integrable (fun ω => (N T ω).toReal ^ 2) P :=
    (avram_anoise18_original_total_negative_count_finite_activity_L2
      X hFinite T).1
  have hB : Integrable B P :=
    (hN2.add (integrable_const A)).add (integrable_const 1)
  have hCounts : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, N t ω < ⊤ := by
    simpa only [N] using
      avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae X hFinite
  have hIdentity (k : ℕ) (t : ℝ≥0) (ω : Ω) :
      S k t ω = R 0 t ω - R k t ω := by
    have hd := avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
      X k 0 t ω
    have hz : S 0 t ω = 0 := by
      simp [S, avram_p4_h_gaussian_intrinsic_small_band_compensated]
    dsimp [R, S] at *
    rw [hz] at hd
    simp only [zero_sub] at hd
    linarith
  refine ⟨B, hB, ?_⟩
  filter_upwards [hCounts] with ω hω
  intro k t ht
  have hNmono : N t ω ≤ N T ω := by
    dsimp [N]
    apply measure_mono
    exact Set.prod_mono
      (by intro u hu; exact ⟨hu.1, hu.2.trans ht⟩)
      (Subset.rfl)
  have hNreal : (N t ω).toReal ≤ (N T ω).toReal :=
    ENNReal.toReal_mono (ne_of_lt (hω T)) hNmono
  have hAt : ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal ≤ A := by
    dsimp [A]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) ENNReal.toReal_nonneg
  have hb := avram_anoise19_original_gaussian_residual_cutoff_count_bound
    X hFinite 0 k (Nat.zero_le k) t ω (hω t)
  have hb' : |R k t ω - R 0 t ω| ≤
      (N t ω).toReal + ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
    simpa [R, N] using hb
  have heq : |S k t ω| = |R k t ω - R 0 t ω| := by
    rw [hIdentity k t ω, abs_sub_comm]
  have hn : 0 ≤ (N T ω).toReal := ENNReal.toReal_nonneg
  have ha : 0 ≤ A := ENNReal.toReal_nonneg
  change ‖S k t ω‖ ≤ B ω
  dsimp [B]
  rw [heq]
  nlinarith [sq_nonneg ((N T ω).toReal - 1)]
