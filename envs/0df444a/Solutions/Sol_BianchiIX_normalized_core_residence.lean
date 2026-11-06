-- Prove2me | solution 1 for BianchiIX.normalized_core_residence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:12:54.84707+00:00
-- url     : https://prove2.me/submissions/296610f0-9536-4419-b519-0cc57a41e00a

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_projectiveOriginal_core_residence
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
open Set


/-- No domain hypothesis is needed: the constrained Einstein flow exists at every forward time. -/
theorem solution {x : NormalizedState} {t₀ k s t : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    (t - s) / k ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      t - s ≤ 2 * k * Real.log (4 * k) := by
  intro β hr hv hu hw
  apply projectiveOriginal_core_residence hk (convex_Icc s t) ?_ hr hv hu hw ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  intro u hh
  have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
  exact hasDerivAt_projectiveOriginalFlow H.1 (ne_of_gt (hA u hh)) H.2.1
