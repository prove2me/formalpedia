-- Prove2me | solution 1 for AvramDividend.Classical.psi_compensated_uniform_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:29:45.597817+00:00
-- url     : https://prove2.me/submissions/e82be2c9-dacf-4a66-b8b5-2248e479976b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- An explicit common majorant on θ in [0,B] for the compensated jump kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : ℝ) (hB : 0 ≤ B) :
    ∀ θ ∈ Icc (0 : ℝ) B,
      ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y‖ ≤
        (1 + B ^ 2) * min 1 (y ^ 2) := by
  intro θ hθ
  have hθzero : 0 ≤ θ := hθ.1
  have hθB : θ ≤ B := hθ.2
  have hsq : θ ^ 2 ≤ B ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hθB) (add_nonneg hθzero hB)]
  filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with y hy
  change y < 0 at hy
  have hz : θ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθzero (le_of_lt hy)
  by_cases hsmall : -1 < y
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    have hy2 : y ^ 2 ≤ 1 := by
      have hp : 0 ≤ (1 + y) * (1 - y) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    obtain ⟨hrlow, hrhigh⟩ := exp_neg_remainder_bounds (θ * y) hz
    have hprod : θ ^ 2 * y ^ 2 ≤ B ^ 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg y)
    have hb :
        |Real.exp (θ * y) - 1 - θ * y| ≤ (1 + B ^ 2) * y ^ 2 := by
      rw [abs_of_nonneg hrlow]
      nlinarith [hprod, sq_nonneg y]
    simpa [Set.indicator, hmem, min_eq_right hy2] using hb
  · have hnot : y ∉ Ioo (-1 : ℝ) 1 :=
      fun h => hsmall h.1
    have hle : y ≤ -1 := le_of_not_gt hsmall
    have hy2 : 1 ≤ y ^ 2 := by
      have hp : 0 ≤ (-y - 1) * (-y + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have he0 : 0 ≤ Real.exp (θ * y) := (Real.exp_pos _).le
    have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hz
    have hb :
        |Real.exp (θ * y) - 1| ≤ (1 + B ^ 2) * 1 := by
      rw [abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg B]
    have hindicator :
        (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 0 := by
      simp [Set.indicator, hnot]
    simpa only [Real.norm_eq_abs, hindicator, mul_zero,
      sub_zero, min_eq_left hy2] using hb
