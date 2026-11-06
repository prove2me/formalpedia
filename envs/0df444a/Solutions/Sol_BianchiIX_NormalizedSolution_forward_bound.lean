-- Prove2me | solution 1 for BianchiIX.NormalizedSolution.forward_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:00:27.220629+00:00
-- url     : https://prove2.me/submissions/0cf333d9-6b09-41b6-8948-dc7417268657

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_normalized_forward_bound
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
    {t : ℝ} (ht : t ∈ S.domain) (htt : t₀ ≤ t) :
    ‖S.curve t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  apply normalized_forward_bound S.convex_domain S.isOpen_domain S.hasDerivAt
    S.initial_mem ht htt (by rw [S.initial_eq]; exact hpos) (by rw [S.initial_eq]; exact hcon)
  intro i
  rw [S.initial_eq]
  exact (le_abs_self _).trans (norm_le_pi_norm x₀ (i.addNat 2))
