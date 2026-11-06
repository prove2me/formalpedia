-- Prove2me | solution 1 for BianchiIX.normalized_core_exit_contraction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:42:07.570333+00:00
-- url     : https://prove2.me/submissions/a36ad58d-eec0-4171-b88c-a8d9cbb5d946

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_scaled_core_exit_contraction
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
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set


/-- The exit estimates for the actual normalized Einstein flow, with its clock constructed by integration. -/
theorem solution {x : NormalizedState} {t₀ k s t : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ u) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    β s 2 = 1 → β t 2 = 1 → 1 ≤ β s 0 →
    1 / (4 * k) ≤ integralClock (normalizedProjectiveRate x t₀) s t ∧
      β t 1 ≤ Real.exp (-k / 40) * β s 1 ∧
      β t 3 ≤ Real.exp (-1 / (2 * k)) * β s 3 := by
  intro β hr hv hu hw hvs hvt hms
  have hdom (u : ℝ) (hh : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hclock (u : ℝ) (hh : u ∈ Icc s t) :
      HasDerivAt (integralClock (normalizedProjectiveRate x t₀) s) (normalizedProjectiveRate x t₀ u) u :=
    (hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (continuousOn_normalizedProjectiveRate x t₀) (hdom s ⟨le_rfl, hst.le⟩) (hdom u hh)).hasDerivAt
  have hsol (u : ℝ) (hh : u ∈ Icc s t) :
      HasDerivAt β (normalizedProjectiveRate x t₀ u • projectiveField (β u)) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hh)) H.2.1
  have H := scaled_core_exit_contraction hk hst hA hsol hclock hr hv hu hw hvs hvt hms
  simpa only [integralClock_initial, sub_zero] using H
