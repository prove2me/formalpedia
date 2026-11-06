-- Prove2me | solution 1 for BianchiIX.projectiveOriginalFlow_core_multipliers_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:59:22.095718+00:00
-- url     : https://prove2.me/submissions/b3d51931-079a-4843-bac8-665f8d71ccae

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toCoreAngleState_scaled
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngleField_auxiliary (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y = ![(coreAuxiliary z y) 3 / (coreAuxiliary z y) 1,
      y 1 * (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1,
      -2 * y 2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1)] := rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngleField_log_rates (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y 1 = y 1 * coreLogRates z y 0 ∧
      coreAngleField z y 2 = y 2 * coreLogRates z y 1 := by
  rw [coreAngleField_auxiliary]
  constructor <;> dsimp [coreLogRates] <;> ring

end
end

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

theorem solution {y : ProjectiveState} {t₀ a b : ℝ}
    (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hreg : ∀ t ∈ Icc a b, let z := projectiveOriginalFlow y t₀ t
      0 < z 2 ∧ projectiveStateDenom z ≠ 0 ∧
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    let β := projectiveOriginalFlow y t₀
    β b 1 = β a 1 * coreFlowMultiplier y t₀ a b 0 ∧
      β b 2 * β b 3 = (β a 2 * β a 3) * coreFlowMultiplier y t₀ a b 1 := by
  intro β
  have hflow (t : ℝ) (ht : t ∈ Icc a b) :=
    hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hc (i : Fin 4) : ContinuousOn (fun t => β t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.mp (hflow t ht) i).continuousAt.continuousWithinAt
  have hr : ContinuousOn (fun t => coreOriginalLogRates (β t)) (Icc a b) := by
    intro t ht
    have hrate := contDiffAt_coreOriginalLogRates 1 (hreg t ht).1 (hreg t ht).2.1 (hreg t ht).2.2
    exact (hrate.continuousAt.comp (hflow t ht).continuousAt).continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Ioo a b) :=
    hasDerivAt_toCoreAngleState_scaled (hflow t (Ioo_subset_Icc_self ht))
      (hreg t (Ioo_subset_Icc_self ht)).1 (hreg t (Ioo_subset_Icc_self ht)).2.2
  have hcoef (t : ℝ) := coreAngleField_log_rates (projectiveCoreAngle (β t)) (toCoreAngleState (β t))
  constructor
  · apply homogeneous_solution_eq_exp_integral_Icc hab (continuousOn_pi.mp hr 0) (hc 1)
    intro t ht
    apply (hasDerivAt_pi.mp (hderiv t ht) 1).congr_deriv
    change coreOriginalClockRate (β t) * coreAngleField (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) 1 = _
    rw [(hcoef t).1]
    dsimp [coreOriginalLogRates, toCoreAngleState]
    ring
  · apply homogeneous_solution_eq_exp_integral_Icc hab (continuousOn_pi.mp hr 1) ((hc 2).mul (hc 3))
    intro t ht
    apply (hasDerivAt_pi.mp (hderiv t ht) 2).congr_deriv
    change coreOriginalClockRate (β t) * coreAngleField (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) 2 = _
    rw [(hcoef t).2]
    dsimp [coreOriginalLogRates, toCoreAngleState]
    ring
