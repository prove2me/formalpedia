-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_forward_of_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:04:41.311199+00:00
-- url     : https://prove2.me/submissions/c3702c31-5f52-4051-bd81-a2fbcb1f75e8

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_NormalizedSolution_forward_bound_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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


theorem solution {x₀ : NormalizedState}
    (hcon : stateConstraint x₀ = 1) {t₀ t : ℝ} (htt : t₀ ≤ t) :
    HasDerivAt (normalizedMaxCurve x₀ t₀) (normalizedField (normalizedMaxCurve x₀ t₀ t)) t ∧
      stateConstraint (normalizedMaxCurve x₀ t₀ t) = 1 ∧
      ‖normalizedMaxCurve x₀ t₀ t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  let S := maximalNormalizedSolution x₀ t₀
  have ht : t ∈ S.domain := normalizedMaxDomain_contains_Ici_of_constraint hcon t₀ htt
  exact ⟨S.hasDerivAt t ht,
    (normalized_constraint_constant S.convex_domain S.hasDerivAt S.initial_mem ht).trans
      ((congrArg stateConstraint S.initial_eq).trans hcon),
    S.forward_bound_of_constraint hcon ht htt⟩
