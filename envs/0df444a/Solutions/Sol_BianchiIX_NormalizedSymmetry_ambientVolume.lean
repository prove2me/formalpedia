-- Prove2me | solution 1 for BianchiIX.NormalizedSymmetry.ambientVolume
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:37:35.905962+00:00
-- url     : https://prove2.me/submissions/a54183c9-ed18-4d9c-a505-9ad4e1dbe881

import Definitions.Def_BianchiIX_Dynamics_SectionFlux
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


theorem solution (v : Fin 5 → NormalizedState) :
    normalizedAmbientVolume (fun i => A.map (v i)) = normalizedAmbientVolume v := by
  have H := (Pi.basisFun ℝ (Fin 5)).det_comp A.map.toLinearMap v
  rw [A.det, one_mul] at H
  convert! H using 1
