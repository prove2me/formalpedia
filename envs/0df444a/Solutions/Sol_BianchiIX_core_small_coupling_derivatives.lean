-- Prove2me | solution 1 for BianchiIX.core_small_coupling_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:58:59.369254+00:00
-- url     : https://prove2.me/submissions/f304e7cc-3fb3-46eb-a7f4-cee26e9b7384

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
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) :
    |u * (s - w / r)| ≤ u ∧ |v - 2 * u + w| ≤ 2 * r := by
  have hr0 : 0 < r := by linarith
  have hwr : 0 ≤ w / r ∧ w / r ≤ 1 :=
    ⟨div_nonneg hw.1 hr0.le, (div_le_one hr0).mpr (by linarith [hw.2, hm.2])⟩
  have hdiff : |s - w / r| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  constructor
  · rw [abs_mul, abs_of_nonneg hu.1]
    exact mul_le_of_le_one_right hu.1 hdiff
  · apply abs_le.mpr
    constructor <;> linarith [hv.1, hv.2, hm.2]
