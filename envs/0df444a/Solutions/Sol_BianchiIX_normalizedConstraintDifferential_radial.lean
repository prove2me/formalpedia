-- Prove2me | solution 1 for BianchiIX.normalizedConstraintDifferential_radial
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:19:42.159034+00:00
-- url     : https://prove2.me/submissions/cd08ec4a-98b4-4191-81c1-2ec40b9f9cf1

import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

theorem solution (x : NormalizedState) :
    normalizedConstraintDifferential x x = 2 * stateConstraint x := by
  have heq (u : ℝ) : stateConstraint (u • x) = u ^ 2 * stateConstraint x := by
    simp only [stateConstraint, constraint, shearSq, curvature, Pi.smul_apply, smul_eq_mul]
    ring
  have H := (hasFDerivAt_stateConstraint ((1 : ℝ) • x)).comp_hasDerivAt 1
    ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hd := ((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (stateConstraint x)
  have H' : HasDerivAt (fun u : ℝ => u ^ 2 * stateConstraint x)
      (normalizedConstraintDifferential x x) 1 := by
    simpa only [Function.comp_def, id_eq, one_smul, heq] using H
  simpa using H'.unique hd
