-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_jump_integrable_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:51:48.241257+00:00
-- url     : https://prove2.me/submissions/7c3ea313-45d4-4ab5-90a7-3fe540541289

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 -
        θ * y * ((Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) X.ν := by
  let f : ℝ → ℝ := fun y =>
    Real.exp (θ * y) - 1 -
      θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
  have hmin_meas : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y =>
      le_min (by norm_num) (sq_nonneg y))
  have hmin_int :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmin_meas.aestronglyMeasurable hmin_nonneg).mp
        (ne_of_lt X.ν_integrable)
  have hdom_int :
      Integrable (fun y : ℝ => (1 + θ ^ 2) * min 1 (y ^ 2)) X.ν :=
    hmin_int.const_mul _
  have hind_meas :
      Measurable (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hf_meas : Measurable f := by
    dsimp [f]
    fun_prop
  have hbound (y : ℝ) (hy : y < 0) :
      |f y| ≤ (1 + θ ^ 2) * min 1 (y ^ 2) := by
    have hz : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
    by_cases hsmall : -1 < y
    · have hmem : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hsmall, by linarith⟩
      have hy2 : y ^ 2 ≤ 1 := by
        have hp : 0 ≤ (1 + y) * (1 - y) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hr := exp_neg_remainder_bounds (θ * y) hz
      have hb :
          |Real.exp (θ * y) - 1 - θ * y| ≤
            (1 + θ ^ 2) * y ^ 2 := by
        rw [abs_of_nonneg hr.1]
        nlinarith [hr.2, sq_nonneg y]
      simpa only [f, Set.indicator_of_mem hmem, mul_one,
        min_eq_right hy2] using hb
    · have hnot : y ∉ Ioo (-1 : ℝ) 1 :=
        fun h => hsmall h.1
      have hle : y ≤ -1 := le_of_not_gt hsmall
      have hy2 : 1 ≤ y ^ 2 := by
        have hp : 0 ≤ (-y - 1) * (-y + 1) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have he0 : 0 ≤ Real.exp (θ * y) :=
        (Real.exp_pos _).le
      have he1 : Real.exp (θ * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr hz
      have hb :
          |Real.exp (θ * y) - 1| ≤
            (1 + θ ^ 2) * 1 := by
        rw [abs_of_nonpos (by linarith)]
        nlinarith [sq_nonneg θ]
      have hindicator :
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y = 0 := by
        simp [Set.indicator, hnot]
      simpa only [f, hindicator, mul_zero,
        sub_zero, min_eq_left hy2] using hb
  apply Integrable.mono' hdom_int.restrict hf_meas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with y hy
  simpa only [Real.norm_eq_abs] using hbound y hy
