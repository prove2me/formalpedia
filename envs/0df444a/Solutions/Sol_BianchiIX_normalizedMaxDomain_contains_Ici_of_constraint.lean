-- Prove2me | solution 1 for BianchiIX.normalizedMaxDomain_contains_Ici_of_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:03:05.051974+00:00
-- url     : https://prove2.me/submissions/d5fbcedc-e87b-428f-bade-ac549c1dbec7

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_NormalizedSolution_forward_bound_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_forward_of_bounds
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

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- Every constraint-one initial state is forward complete, including all zero-wall faces. -/
theorem solution {x₀ : NormalizedState}
    (hcon : stateConstraint x₀ = 1) (t₀ : ℝ) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by
  apply normalizedMaxDomain_forward_of_bounds
  intro T
  refine ⟨1 + 3 * ‖x₀‖ * Real.exp (T - t₀), by positivity, fun t ht htt => ?_⟩
  apply ((maximalNormalizedSolution x₀ t₀).forward_bound_of_constraint hcon ht htt.1).trans
  gcongr
  exact htt.2
