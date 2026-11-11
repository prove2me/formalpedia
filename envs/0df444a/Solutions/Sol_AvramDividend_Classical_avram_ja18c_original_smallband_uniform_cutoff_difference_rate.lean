-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18c_original_smallband_uniform_cutoff_difference_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:49:59.784905+00:00
-- url     : https://prove2.me/submissions/e8f74e15-1adf-4331-b510-d8935ca324ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Uniform cutoff Cauchy modulus for the literal original marked jump path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (ω : Ω)
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    ∀ n m : ℕ, n ≤ m → ∀ t : ℝ≥0, t ≤ T →
      |avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω| ≤
      (1 / ((n : ℝ) + 1)) *
        ((((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal +
        ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by
  let R (k : ℕ) (t : ℝ≥0) :=
    avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω
  let S (k : ℕ) (t : ℝ≥0) :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω
  let N (t : ℝ≥0) : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  let A (t : ℝ≥0) : ℝ :=
    ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  intro n m hnm t ht
  have hNmono : N t ≤ N T := by
    dsimp [N]
    apply measure_mono
    exact Set.prod_mono
      (by intro u hu; exact ⟨hu.1, hu.2.trans ht⟩)
      (Subset.rfl)
  have hNt : N t < ⊤ := lt_of_le_of_lt hNmono hNfin
  have hNreal : (N t).toReal ≤ (N T).toReal :=
    ENNReal.toReal_mono (ne_of_lt hNfin) hNmono
  have hAt : A t ≤ A T := by
    dsimp [A]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) ENNReal.toReal_nonneg
  have hDiff := avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
    X n m t ω
  have hIdentity : S m t - S n t = R n t - R m t := by
    simpa only [R, S] using hDiff.symm
  have hBound := avram_anoise19_original_gaussian_residual_cutoff_count_bound
    X hFinite n m hnm t ω hNt
  have hb : |R m t - R n t| ≤
      (1 / ((n : ℝ) + 1)) * ((N t).toReal + A t) := by
    simpa only [R, N, A] using hBound
  change |S m t - S n t| ≤
    (1 / ((n : ℝ) + 1)) * ((N T).toReal + A T)
  calc
    |S m t - S n t| = |R n t - R m t| := by rw [hIdentity]
    _ = |R m t - R n t| := abs_sub_comm _ _
    _ ≤ (1 / ((n : ℝ) + 1)) * ((N t).toReal + A t) := hb
    _ ≤ (1 / ((n : ℝ) + 1)) * ((N T).toReal + A T) :=
      mul_le_mul_of_nonneg_left (add_le_add hNreal hAt) (by positivity)
