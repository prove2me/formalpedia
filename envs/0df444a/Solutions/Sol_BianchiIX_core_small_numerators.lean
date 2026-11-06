-- Prove2me | solution 1 for BianchiIX.core_small_numerators
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:03:54.830197+00:00
-- url     : https://prove2.me/submissions/c5d0d2e9-38a0-4dd4-a6c7-e521e35b6f0e

import Definitions.Def_BianchiIX_Algebra_Projective
import Theorems.Thm_BianchiIX_core_small_coupling
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

private theorem BianchiIX.core_wall_difference_bounds {m u w : ℝ} (hu : 0 ≤ u ∧ u ≤ m)
    (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| ≤ m ∧ |u - 2 * w| ≤ 2 * m ∧ |3 * w - u| ≤ 3 * m ∧ |2 * u - w| ≤ 2 * m := by
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem solution {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hrm : r * m ≤ 1 / 1000)
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) (hv : 1 ≤ v ∧ v ≤ r)
    (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-r / 2 - c + s * w + (u ^ 2 - w ^ 2) / (2 * r)| ≤ r ∧
    |-coupling u v w + c * (u - w) ^ 2 / r| ≤ 2 * r * m := by
  have hr0 : 0 < r := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hu.1 (by norm_num)).mpr (hu.2.trans hm.2)
  have hw2 : w ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hw.1 (by norm_num)).mpr (hw.2.trans hm.2)
  have hsw : 0 ≤ s * w ∧ s * w ≤ m :=
    ⟨mul_nonneg hs.1 hw.1, (mul_le_of_le_one_left hw.1 hs.2).trans hw.2⟩
  have he : |(u ^ 2 - w ^ 2) / (2 * r)| ≤ 1 / 100 := by
    rw [abs_div, abs_of_pos (show 0 < 2 * r by positivity), div_le_iff₀ (by positivity)]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg u, sq_nonneg w]
  constructor
  · have H := abs_add_le (-r / 2 - c + s * w) ((u ^ 2 - w ^ 2) / (2 * r))
    have H' := abs_add_le (-r / 2 - c) (s * w)
    have H'' := abs_sub (-r / 2) c
    have hhalf : |(-r / 2)| = r / 2 := by rw [abs_div, abs_neg, abs_of_pos hr0]; norm_num
    rw [hhalf] at H''
    rw [abs_of_nonneg hsw.1] at H'
    linarith [hm.2]
  · obtain ⟨hC0, hC, _⟩ := core_small_coupling hm hrm hu hw hv
    have hdelta := (core_wall_difference_bounds hu hw).1
    have hdelta2 : (u - w) ^ 2 ≤ m ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hm.1).mpr hdelta
    have he' : |c * (u - w) ^ 2 / r| ≤ m ^ 2 / r := by
      simp only [abs_div, abs_mul, abs_of_pos hr0, abs_of_nonneg (sq_nonneg (u - w))]
      exact div_le_div_of_nonneg_right
        ((mul_le_of_le_one_left (sq_nonneg _) hc).trans hdelta2) hr0.le
    have he'' : m ^ 2 / r ≤ m ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    have H := abs_add_le (-coupling u v w) (c * (u - w) ^ 2 / r)
    rw [abs_neg, abs_of_nonneg hC0] at H
    have hsmall : 2 * m ^ 2 ≤ r * m := by nlinarith [mul_nonneg hm.1 (show 0 ≤ r - 2 * m by linarith [hm.2])]
    linarith
