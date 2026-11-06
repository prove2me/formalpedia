-- Prove2me | solution 1 for BianchiIX.core_small_strong_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:59:46.421823+00:00
-- url     : https://prove2.me/submissions/482d9435-9505-44c4-aa88-3b0382e1923b

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {r m u v w s : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v) (hs : 0 ≤ s ∧ s ≤ 1) :
    |-1 / 2 - s * w / r + (3 * w ^ 2 - u ^ 2) / (2 * r ^ 2)| ≤ 3 / 4 ∧
    |(1 - w / v) / r| ≤ 1 / r := by
  have hr0 : 0 < r := by linarith
  have hv0 : 0 < v := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hu.1 (by norm_num)).mpr (hu.2.trans hm.2)
  have hw2 : w ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hw.1 (by norm_num)).mpr (hw.2.trans hm.2)
  have hsw : 0 ≤ s * w ∧ s * w ≤ 1 / 100 :=
    ⟨mul_nonneg hs.1 hw.1, ((mul_le_of_le_one_left hw.1 hs.2).trans hw.2).trans hm.2⟩
  have hfirst : |s * w / r| ≤ 1 / 100 := by
    rw [abs_of_nonneg (div_nonneg hsw.1 hr0.le)]
    exact (div_le_self hsw.1 (by linarith)).trans hsw.2
  have hsecond : |(3 * w ^ 2 - u ^ 2) / (2 * r ^ 2)| ≤ 1 / 100 := by
    rw [abs_div, abs_of_pos (show 0 < 2 * r ^ 2 by positivity), div_le_iff₀ (by positivity)]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (r - 5), sq_nonneg u, sq_nonneg w]
  constructor
  · have H := abs_add_le (-1 / 2 - s * w / r) ((3 * w ^ 2 - u ^ 2) / (2 * r ^ 2))
    have H' := abs_sub (-1 / 2 : ℝ) (s * w / r)
    norm_num at H'
    linarith
  · rw [abs_div, abs_of_pos hr0]
    apply div_le_div_of_nonneg_right _ hr0.le
    apply abs_le.mpr
    have hwr : 0 ≤ w / v ∧ w / v ≤ 1 :=
      ⟨div_nonneg hw.1 hv0.le, (div_le_one hv0).mpr (by linarith [hw.2, hm.2])⟩
    constructor <;> linarith
