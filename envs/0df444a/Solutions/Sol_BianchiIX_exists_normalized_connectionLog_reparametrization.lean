-- Prove2me | solution 1 for BianchiIX.exists_normalized_connectionLog_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:56:32.566374+00:00
-- url     : https://prove2.me/submissions/bfe147d9-b761-4c43-9afb-09816f17064b

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_exists_scaled_connectionLog_reparametrization
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

theorem solution {x : NormalizedState} {t₀ s : ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ t ∈ I, 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hw : ∀ t ∈ I, 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 3)
    (hD : ∀ t ∈ I, 0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ t))) :
    let β := fun t => toProjectiveState (normalizedMaxCurve x t₀ t)
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = Real.log (β t 3) - Real.log (β s 3)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        HasDerivAt e.symm (1 / ((1 + normalizedMaxCurve x t₀ (e.symm z) 0) *
          connectionClockRate (β (e.symm z)))) z ∧
        β (e.symm z) 3 = β s 3 * Real.exp z ∧
        HasDerivAt (fun u => β (e.symm u)) (connectionLogField (β (e.symm z))) z) := by
  apply exists_scaled_connectionLog_reparametrization
    (a := fun t => 1 + normalizedMaxCurve x t₀ t 0) hI ho hs ?_ hA ?_ hw hD
  · intro t ht
    exact (continuousAt_const.add (hasDerivAt_pi.mp
      (hasDerivAt_normalizedMaxCurve (hdom ht)) 0).continuousAt).continuousWithinAt
  · intro t ht
    exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom ht))
      (ne_of_gt (hA t ht)) ((normalizedMaxCurve_constraint (hdom ht)).trans hc)
