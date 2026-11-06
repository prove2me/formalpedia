-- Prove2me | solution 1 for BianchiIX.hasDerivAt_rootExtension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:39:17.330952+00:00
-- url     : https://prove2.me/submissions/f3738a42-5916-4076-9e62-c74e005634f5

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_hasDerivAt_rootPrimitive
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


theorem solution {s e : ℝ} (hs : 0 < s) (he : |e| = 1) (d x : ℝ) :
    HasDerivAt (rootExtension s d e) (d * rootCutoff (e * x / s)) x := by
  have he2 : e ^ 2 = 1 := by nlinarith [sq_abs e]
  have h := (((hasDerivAt_rootPrimitive (e * x / s)).comp x
    (((hasDerivAt_id x).const_mul e).div_const s)).const_mul (e * d * s)).const_add s
  convert! h using 1
  field_simp
  ring_nf
  simp [he2]
