-- Prove2me | solution 1 for BianchiIX.NormalizedSolution.physical
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:59:30.527195+00:00
-- url     : https://prove2.me/submissions/40574afe-eacf-4b9a-a0b3-ccc939839141

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_positive_walls_invariant
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


theorem solution {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1)
    {t : ℝ} (ht : t ∈ S.domain) :
    positiveWalls (S.curve t) ∧ stateConstraint (S.curve t) = 1 := by
  refine ⟨normalized_positive_walls_invariant S.convex_domain S.isOpen_domain S.hasDerivAt
    S.initial_mem ht (by rw [S.initial_eq]; exact hpos), ?_⟩
  exact (normalized_constraint_constant S.convex_domain S.hasDerivAt S.initial_mem ht).trans
    ((congrArg stateConstraint S.initial_eq).trans hcon)
