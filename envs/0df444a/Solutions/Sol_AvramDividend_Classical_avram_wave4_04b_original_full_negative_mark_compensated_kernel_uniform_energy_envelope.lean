-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:19:02.679287+00:00
-- url     : https://prove2.me/submissions/1f096734-e4b6-4145-a28e-4b1dade2fe81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, y ∈ Icc (u + δ) v →
      ∀ z : ℝ, z < 0 →
        (w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0)) ^ 2 ≤
          K * min 1 (z ^ 2) := by
  obtain ⟨K₀, hK₀, hinc, _⟩ :=
    avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
      X w a b u v δ hw hw_cont hw_neg hau huv hvb hu0 hδ hδone hband
  have hau' : a < u + δ := by linarith
  obtain ⟨M, hM, hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval
      w a b (u + δ) v hw hau' hband hvb
  have hK : 0 ≤ 2 * K₀ + 2 * M ^ 2 := by
    nlinarith [sq_nonneg M]
  refine ⟨2 * K₀ + 2 * M ^ 2, hK, ?_⟩
  intro y hy z hz
  have hinc' := hinc y hy z hz
  have hMabs := hderiv y hy.1 hy.2
  have hsq : (deriv w y) ^ 2 ≤ M ^ 2 := by
    have hleft := (abs_le.mp hMabs).1
    have hright := (abs_le.mp hMabs).2
    have hnonneg₁ : 0 ≤ M - deriv w y := by linarith
    have hnonneg₂ : 0 ≤ M + deriv w y := by linarith
    nlinarith [mul_nonneg hnonneg₁ hnonneg₂]
  have hmin : 0 ≤ min (1 : ℝ) (z ^ 2) :=
    le_min (by norm_num) (sq_nonneg z)
  have hcomp :
      (if -1 < z then z * deriv w y else 0) ^ 2 ≤
        M ^ 2 * min 1 (z ^ 2) := by
    by_cases hz1 : -1 < z
    · have hzsq : z ^ 2 ≤ 1 := by
        have h₁ : 0 ≤ z + 1 := by linarith
        have h₂ : 0 ≤ 1 - z := by linarith
        nlinarith [mul_nonneg h₁ h₂]
      rw [if_pos hz1, min_eq_right hzsq]
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg z)]
    · simpa [hz1] using (mul_nonneg (sq_nonneg M) hmin)
  calc
    (w (y + z) - w y -
      (if -1 < z then z * deriv w y else 0)) ^ 2 ≤
      2 * (w (y + z) - w y) ^ 2 +
        2 * (if -1 < z then z * deriv w y else 0) ^ 2 := by
        nlinarith [sq_nonneg
          ((w (y + z) - w y) +
            (if -1 < z then z * deriv w y else 0))]
    _ ≤ 2 * (K₀ * min 1 (z ^ 2)) +
          2 * (M ^ 2 * min 1 (z ^ 2)) := by
          nlinarith [hinc', hcomp]
    _ = (2 * K₀ + 2 * M ^ 2) * min 1 (z ^ 2) := by ring
