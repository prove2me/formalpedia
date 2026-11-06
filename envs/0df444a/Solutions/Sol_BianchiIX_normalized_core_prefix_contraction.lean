-- Prove2me | solution 1 for BianchiIX.normalized_core_prefix_contraction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:07:40.74646+00:00
-- url     : https://prove2.me/submissions/cbf14edd-45f4-4eff-aa6f-de9b3c812fd3

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_scaled_core_prefix_contraction
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

theorem solution {x : NormalizedState} {t₀ k s t : ℝ} {I : Set ℝ}
    (hk : 6 ≤ k) (hI : Convex ℝ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ u ∈ I, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2)) →
    (∀ u ∈ I, 1 ≤ β u 2) →
    (∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    β t 1 ≤ β s 1 * Real.exp (-k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4) ∧
      β t 2 * β t 3 ≤ β s 2 * β s 3 := by
  intro β hr hv hu hw
  apply scaled_core_prefix_contraction (a := fun u => 1 + normalizedMaxCurve x t₀ u 0)
    hk hI hA ?_ hr hv hu hw hs ht hst
  intro u hu
  exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom hu))
    (ne_of_gt (hA u hu)) ((normalizedMaxCurve_constraint (hdom hu)).trans hc)
