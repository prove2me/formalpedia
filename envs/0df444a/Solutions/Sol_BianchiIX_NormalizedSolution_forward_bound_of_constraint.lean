-- Prove2me | solution 1 for BianchiIX.NormalizedSolution.forward_bound_of_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:59:59.619059+00:00
-- url     : https://prove2.me/submissions/80336b9c-75b8-44fe-aea0-6c748cf66861

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_normalizedState_norm_bound_abs
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_wall_abs_growth
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


theorem solution {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) (hcon : stateConstraint x₀ = 1)
    {t : ℝ} (ht : t ∈ S.domain) (htt : t₀ ≤ t) :
    ‖S.curve t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  have hc : stateConstraint (S.curve t) = 1 :=
    (normalized_constraint_constant S.convex_domain S.hasDerivAt S.initial_mem ht).trans
      ((congrArg stateConstraint S.initial_eq).trans hcon)
  have H := normalizedState_norm_bound_abs hc (fun i =>
    (normalized_wall_abs_growth S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem ht htt i).trans
      (mul_le_mul_of_nonneg_right
        (show |wallValue i (S.curve t₀)| ≤ ‖x₀‖ by
          rw [S.initial_eq]
          exact norm_le_pi_norm x₀ (i.addNat 2)) (Real.exp_pos _).le))
  simpa only [mul_assoc] using H
