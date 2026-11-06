-- Prove2me | solution 1 for BianchiIX.normalizedMaxDomain_contains_Ici
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:02:51.117207+00:00
-- url     : https://prove2.me/submissions/d1082feb-b25e-4b93-93c0-8b62c4be3089

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_NormalizedSolution_forward_bound
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
open Set Filter Metric
open scoped Topology


/-- Physical initial data for the exact normalized Einstein ODE are forward complete. -/
theorem solution {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1) (t₀ : ℝ) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by
  apply normalizedMaxDomain_forward_of_bounds
  intro T
  refine ⟨1 + 3 * ‖x₀‖ * Real.exp (T - t₀), by positivity, fun t ht htt => ?_⟩
  apply ((maximalNormalizedSolution x₀ t₀).forward_bound hpos hcon ht htt.1).trans
  gcongr
  exact htt.2
