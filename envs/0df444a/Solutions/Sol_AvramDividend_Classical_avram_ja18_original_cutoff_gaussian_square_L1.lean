-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:16:55.569899+00:00
-- url     : https://prove2.me/submissions/47d667e7-2125-4c11-baa4-1e1e0d86488e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_original_zero_cutoff_gaussian_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every finite cutoff inherits square integrability from the zero cutoff,
using the original physical negative-jump count L² estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n t
  let G : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  let B : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  let A : ℝ := ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  have hB : Integrable (fun ω => (B ω) ^ 2) P := by
    simpa only [B] using
      (avram_ja18i_original_zero_cutoff_gaussian_square_integrable X hX hFinite t)
  have hN : Integrable (fun ω => (N ω).toReal ^ 2) P := by
    simpa only [N] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2
        X hFinite t).1
  have hNfin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards
      [avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
        X hFinite] with ω hω
    exact hω t
  have hDom : Integrable
      (fun ω => 2 * (B ω) ^ 2 + 4 * (N ω).toReal ^ 2 + 4 * A ^ 2) P := by
    exact ((hB.const_mul 2).add (hN.const_mul 4)).add
      (integrable_const (4 * A ^ 2 : ℝ))
  have hMeas : AEStronglyMeasurable (fun ω => (G ω) ^ 2) P := by
    have hG : Measurable G :=
      (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
        X n t).mono (𝓕.le t) le_rfl
    have hGG : Measurable (fun ω => G ω * G ω) := hG.mul hG
    simpa only [pow_two] using hGG.aestronglyMeasurable
  change Integrable (fun ω => (G ω) ^ 2) P
  apply hDom.mono hMeas
  filter_upwards [hNfin] with ω hω
  have hBound : |G ω - B ω| ≤ (N ω).toReal + A := by
    have hSource :=
      avram_anoise19_original_gaussian_residual_cutoff_count_bound
        X hFinite 0 n (Nat.zero_le n) t ω hω
    simpa [G, B, N, A] using hSource
  have hTwo := abs_le.mp hBound
  have hUpper : 0 ≤
      ((N ω).toReal + A - (G ω - B ω)) *
        ((N ω).toReal + A + (G ω - B ω)) := by
    apply mul_nonneg
    · linarith [hTwo.2]
    · linarith [hTwo.1]
  have hSquare : (G ω) ^ 2 ≤
      2 * (B ω) ^ 2 + 4 * (N ω).toReal ^ 2 + 4 * A ^ 2 := by
    nlinarith [hUpper, sq_nonneg (G ω - 2 * B ω),
      sq_nonneg ((N ω).toReal - A)]
  have hGnonneg : 0 ≤ (G ω) ^ 2 := sq_nonneg _
  have hDnonneg :
      0 ≤ 2 * (B ω) ^ 2 + 4 * (N ω).toReal ^ 2 + 4 * A ^ 2 := by
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hGnonneg,
    abs_of_nonneg hDnonneg] using hSquare
