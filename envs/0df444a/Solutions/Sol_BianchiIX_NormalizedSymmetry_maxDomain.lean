-- Prove2me | solution 1 for BianchiIX.NormalizedSymmetry.maxDomain
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:50:44.536037+00:00
-- url     : https://prove2.me/submissions/98bb5b9b-a9f6-4a5f-8c25-35d7590c9f8c

import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic


noncomputable section
open BianchiIX
open Set
open BianchiIX.NormalizedSymmetry
variable (A : NormalizedSymmetry)


theorem solution (x : NormalizedState) (t₀ : ℝ) :
    normalizedMaxDomain (A.map x) t₀ = normalizedMaxDomain x t₀ := by
  apply Subset.antisymm
  · intro t ht
    have H := ((maximalNormalizedSolution (A.map x) t₀).transform A.symm).domain_subset_maximal ht
    simpa only [BianchiIX.NormalizedSymmetry.symm, ContinuousLinearEquiv.symm_apply_apply] using H
  · exact ((maximalNormalizedSolution x t₀).transform A).domain_subset_maximal
