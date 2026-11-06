-- Prove2me | solution 1 for BianchiIX.rootPrimitive_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:39:32.409859+00:00
-- url     : https://prove2.me/submissions/7926ef75-05da-4311-92de-9232371fe6da

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_rootPrimitive_after_one
import Theorems.Thm_BianchiIX_rootPrimitive_on_unit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ rootPrimitive t ∧ rootPrimitive t ≤ 1 / 2 := by
  rcases le_total t 1 with h | h
  · rw [rootPrimitive_on_unit ⟨ht, h⟩]
    constructor <;> nlinarith [mul_nonneg ht (sub_nonneg.mpr h), sq_nonneg (t - 1)]
  · rw [rootPrimitive_after_one h]
    norm_num
