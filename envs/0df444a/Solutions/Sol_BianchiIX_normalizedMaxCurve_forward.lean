-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_forward
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:04:20.379733+00:00
-- url     : https://prove2.me/submissions/23112dab-685b-4883-8271-59f39d5a6e4a

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_NormalizedSolution_forward_bound
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
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


theorem solution {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1) {t₀ t : ℝ} (htt : t₀ ≤ t) :
    HasDerivAt (normalizedMaxCurve x₀ t₀) (normalizedField (normalizedMaxCurve x₀ t₀ t)) t ∧
      positiveWalls (normalizedMaxCurve x₀ t₀ t) ∧
      stateConstraint (normalizedMaxCurve x₀ t₀ t) = 1 ∧
      ‖normalizedMaxCurve x₀ t₀ t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  let S := maximalNormalizedSolution x₀ t₀
  have ht : t ∈ S.domain := normalizedMaxDomain_contains_Ici hpos hcon t₀ htt
  have hp := S.physical hpos hcon ht
  exact ⟨S.hasDerivAt t ht, hp.1, hp.2, S.forward_bound hpos hcon ht htt⟩
