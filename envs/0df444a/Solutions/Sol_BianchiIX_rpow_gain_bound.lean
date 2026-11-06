-- Prove2me | solution 1 for BianchiIX.rpow_gain_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:32:17.656404+00:00
-- url     : https://prove2.me/submissions/a2613599-1ab4-4938-a0d0-ff913873f6c9

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- A budget at the largest amplitude remains valid at every smaller scale. -/
theorem solution {B Bmax C p q : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hC : 0 ≤ C) (hpq : q ≤ p) (hbudget : C * Bmax ^ (p - q) ≤ 1) :
    C * B ^ p ≤ B ^ q := by
  have hs : C * B ^ (p - q) ≤ 1 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hB.le hmax (sub_nonneg.mpr hpq)) hC).trans hbudget
  calc
    C * B ^ p = (C * B ^ (p - q)) * B ^ q := by
      rw [mul_assoc, ← Real.rpow_add hB, sub_add_cancel]
    _ ≤ 1 * B ^ q := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hB.le _)
    _ = B ^ q := one_mul _
