-- Prove2me | solution 1 for BianchiIX.NormalizedSymmetry.maxCurve
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:37:33.089166+00:00
-- url     : https://prove2.me/submissions/6da31012-575f-48b5-95d8-c3694884ae72

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


theorem solution {x : NormalizedState} {t₀ t : ℝ} (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (A.map x) t₀ t = A.map (normalizedMaxCurve x t₀ t) :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).transform A) ht
