-- Prove2me | solution 1 for AvramDividend.Classical.esscher_discounted_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:00:50.792991+00:00
-- url     : https://prove2.me/submissions/62240193-1ca8-4c59-8366-1c70f1c88568

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ≥0) (φ : ℝ) (hφ : 0 < φ)
    (hJ : Integrable (fun z : ℝ≥0 =>
      1 - Real.exp (-(φ * (z : ℝ)))) ν) :
    Integrable (fun z : ℝ≥0 =>
      (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ν := by
  have hmajor : Integrable
      (fun z : ℝ≥0 => φ⁻¹ * (1 - Real.exp (-(φ * (z : ℝ))))) ν :=
    hJ.const_mul φ⁻¹
  apply Integrable.mono hmajor (by fun_prop)
  filter_upwards with z
  have hz : 0 ≤ (z : ℝ) := NNReal.coe_nonneg z
  have hθ : 0 ≤ φ * (z : ℝ) := mul_nonneg hφ.le hz
  have hle : φ * (z : ℝ) ≤ Real.exp (φ * (z : ℝ)) - 1 := by
    linarith [Real.add_one_le_exp (φ * (z : ℝ))]
  have hmul :=
    mul_le_mul_of_nonneg_right hle (Real.exp_pos (-(φ * (z : ℝ)))).le
  have he : Real.exp (φ * (z : ℝ)) *
      Real.exp (-(φ * (z : ℝ))) = 1 := by
    rw [← Real.exp_add]
    simp
  have hbound :
      (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ≤
      (1 - Real.exp (-(φ * (z : ℝ)))) / φ := by
    apply (le_div_iff₀ hφ).2
    calc
      (z : ℝ) * Real.exp (-(φ * (z : ℝ))) * φ =
        (φ * (z : ℝ)) * Real.exp (-(φ * (z : ℝ))) := by ring
      _ ≤ (Real.exp (φ * (z : ℝ)) - 1) *
            Real.exp (-(φ * (z : ℝ))) := hmul
      _ = 1 - Real.exp (-(φ * (z : ℝ))) := by
        rw [sub_mul, he, one_mul]
  have hnonneg :
      0 ≤ 1 - Real.exp (-(φ * (z : ℝ))) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hθ)
  have hzpos :
      0 ≤ (z : ℝ) * Real.exp (-(φ * (z : ℝ))) :=
    mul_nonneg hz (Real.exp_pos _).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hzpos,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hφ.le) hnonneg)]
  simpa only [div_eq_mul_inv, mul_comm] using hbound
