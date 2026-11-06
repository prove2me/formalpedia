-- Prove2me | solution 1 for BianchiIX.NormalizedSymmetry.constraintVolume
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:54:30.100171+00:00
-- url     : https://prove2.me/submissions/0b2ab1cd-51ac-49f0-9330-499335eb9483

import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSymmetry_ambientVolume
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


theorem solution (x : NormalizedState) (v : Fin 4 → NormalizedState) :
    normalizedConstraintVolume (A.map x) (fun i => A.map (v i)) = normalizedConstraintVolume x v := by
  unfold normalizedConstraintVolume
  rw [← map_smul, A.weight]
  have H := A.ambientVolume (Fin.cons ((1 / 2 : ℝ) • x) v)
  change normalizedAmbientVolume (A.map ∘ Fin.cons ((1 / 2 : ℝ) • x) v) = _ at H
  rw [Fin.comp_cons] at H
  exact congrArg (fun z => z / normalizedVolumeWeight x) H
