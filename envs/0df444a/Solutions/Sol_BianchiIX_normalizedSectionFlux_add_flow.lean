-- Prove2me | solution 1 for BianchiIX.normalizedSectionFlux_add_flow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:54:22.577204+00:00
-- url     : https://prove2.me/submissions/1873288e-965b-493f-99e2-7fe02e0444ad

import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Theorems.Thm_BianchiIX_alternating_fin5_add_flow
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
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic

noncomputable section
open BianchiIX
open Set


theorem solution (x X : NormalizedState)
    (v : Fin 3 → NormalizedState) (c : Fin 3 → ℝ) :
    normalizedAmbientVolume (Fin.cons X (Fin.cons (normalizedField x)
        (fun i => v i + c i • normalizedField x))) =
      normalizedAmbientVolume (Fin.cons X (Fin.cons (normalizedField x) v)) := by
  have hleft : Fin.cons X (Fin.cons (normalizedField x) (fun i => v i + c i • normalizedField x)) =
      ![X, normalizedField x, v 0 + c 0 • normalizedField x,
        v 1 + c 1 • normalizedField x, v 2 + c 2 • normalizedField x] := by
    ext i
    fin_cases i <;> rfl
  have hright : Fin.cons X (Fin.cons (normalizedField x) v) =
      ![X, normalizedField x, v 0, v 1, v 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hleft, hright]
  exact alternating_fin5_add_flow normalizedAmbientVolume X (normalizedField x)
    (v 0) (v 1) (v 2) (c 0) (c 1) (c 2)
