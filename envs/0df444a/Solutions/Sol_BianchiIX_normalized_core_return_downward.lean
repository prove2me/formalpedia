-- Prove2me | solution 1 for BianchiIX.normalized_core_return_downward
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:12:13.629898+00:00
-- url     : https://prove2.me/submissions/8e87aee0-1895-4481-a911-059888be102a

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_scaled_core_return_downward
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ t 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    β t 2 = 1 → (∀ u ∈ Ioo s t, 1 ≤ β u 2) →
    99 / 100 * k ≤ coreRadius (β t 0) (β t 2) →
    (0 ≤ β t 1 ∧ β t 1 ≤ (1 / 10000) / k) →
    (0 ≤ β t 3 ∧ β t 3 ≤ (1 / 10000) / k) →
    β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 ∧
      ∀ᶠ u in 𝓝[>] t, β u 2 < 1 := by
  intro β hv habove hr hu hw
  have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hst.le)
  exact scaled_core_return_downward hk hst hA
    (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt hA) H.2.1) hv habove hr hu hw
