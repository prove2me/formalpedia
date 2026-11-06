-- Prove2me | solution 1 for BianchiIX.NormalizedSymmetry.sectionFlux
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:03:04.311194+00:00
-- url     : https://prove2.me/submissions/b578e154-dabf-4797-b850-8a4c19e1d583

import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSymmetry_constraintVolume
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


theorem solution (x : NormalizedState) (v : Fin 3 → NormalizedState) :
    normalizedSectionFlux (A.map x) (fun i => A.map (v i)) = normalizedSectionFlux x v := by
  unfold normalizedSectionFlux
  rw [A.field]
  have H := A.constraintVolume x (Fin.cons (normalizedField x) v)
  change normalizedConstraintVolume (A.map x) (A.map ∘ Fin.cons (normalizedField x) v) = _ at H
  rw [Fin.comp_cons] at H
  exact H
