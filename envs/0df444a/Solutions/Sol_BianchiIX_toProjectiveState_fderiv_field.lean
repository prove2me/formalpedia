-- Prove2me | solution 1 for BianchiIX.toProjectiveState_fderiv_field
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:33:31.726201+00:00
-- url     : https://prove2.me/submissions/7b1b4d0d-bdb1-459a-a8ec-2b12b762d17e

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    fderiv ℝ toProjectiveState x (normalizedField x) =
      (1 + x 0) • projectiveField (toProjectiveState x) := by
  let alpha : ℝ → NormalizedState := fun t => x + t • normalizedField x
  have hbase : alpha 0 = x := by simp [alpha]
  have hα : HasDerivAt alpha (normalizedField x) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (normalizedField x)) using 1
    simp
  have hd := ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hbase.symm ▸ hd).comp_hasDerivAt 0 hα
  have H' := hasDerivAt_toProjectiveState_normalized
    (show HasDerivAt alpha (normalizedField (alpha 0)) 0 by simpa [hbase] using hα)
    (by simpa [hbase] using hA) (by simpa [hbase] using hc)
  simpa only [hbase] using H.unique H'
