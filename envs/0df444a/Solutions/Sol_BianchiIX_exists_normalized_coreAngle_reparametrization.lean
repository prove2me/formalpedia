-- Prove2me | solution 1 for BianchiIX.exists_normalized_coreAngle_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:42:50.692783+00:00
-- url     : https://prove2.me/submissions/a0b55e5b-ed17-4d8c-9833-e009236529dc

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_exists_scaled_coreAngle_reparametrization
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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

/-- The exact normalized Einstein flow satisfies the angle system on every positive-clock interval. -/
theorem solution {x : NormalizedState} {t₀ s : ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ t ∈ I, 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hv : ∀ t ∈ I, 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 2)
    (hd : ∀ t ∈ I, let y := toProjectiveState (normalizedMaxCurve x t₀ t)
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3)) :
    let β := fun t => toProjectiveState (normalizedMaxCurve x t₀ t)
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        coreAngle (β (e.symm z) 0) (β (e.symm z) 2) = z + coreAngle (β s 0) (β s 2) ∧
        HasDerivAt (fun u => toCoreAngleState (β (e.symm u)))
          (coreAngleField (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z)))) z ∧
        fromCoreAngleState (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z))) = β (e.symm z)) := by
  apply exists_scaled_coreAngle_reparametrization (a := fun t => 1 + normalizedMaxCurve x t₀ t 0)
    hI ho hs ?_ hA ?_ hv hd
  · intro t ht
    exact (continuousAt_const.add (hasDerivAt_pi.mp
      (hasDerivAt_normalizedMaxCurve (hdom ht)) 0).continuousAt).continuousWithinAt
  · intro t ht
    exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom ht))
      (ne_of_gt (hA t ht)) ((normalizedMaxCurve_constraint (hdom ht)).trans hc)
