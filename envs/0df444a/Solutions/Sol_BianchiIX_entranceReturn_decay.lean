-- Prove2me | solution 1 for BianchiIX.entranceReturn_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:18:50.958226+00:00
-- url     : https://prove2.me/submissions/d26d408b-7384-4184-8877-5e583eb0ac48

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_entrance_decay
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

end
end

theorem solution {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let k := coreRadius (y 0) (y 2)
    let L := -Real.log (y 2)
    entranceReturnState y 1 ≤ y 1 * y 2 * Real.exp (-k * L / 3) ∧
      entranceReturnState y 3 ≤ y 3 * y 2 * Real.exp (-L / k) := by
  intro k L
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have ht : 0 ≤ entranceReturnTime y := HR.1.1.1.le
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have H := normalized_entrance_decay hc hk le_rfl ht (fun r hr => (HR.2.1 r hr).2)
    (entranceReturn_region hk hm hu hv hw)
    (by change 0 < projectiveOriginalFlow y 0 0 2; rw [hinit]; exact hv.1)
    (entranceReturnTime y) ⟨ht, le_rfl⟩
  change entranceReturnState y 1 ≤ projectiveOriginalFlow y 0 0 1 *
      Real.exp (-(1 + k / 3) * (Real.log (entranceReturnState y 2) - Real.log (projectiveOriginalFlow y 0 0 2))) ∧
    entranceReturnState y 3 ≤ projectiveOriginalFlow y 0 0 3 *
      Real.exp (-(1 + 1 / k) * (Real.log (entranceReturnState y 2) - Real.log (projectiveOriginalFlow y 0 0 2))) at H
  rw [hinit, (entranceReturn_active_component hk hm hu hv hw).1, Real.log_one, zero_sub] at H
  have he (a : ℝ) : Real.exp (-(1 + a) * L) = y 2 * Real.exp (-a * L) := by
    rw [show -(1 + a) * L = -L + -a * L by ring, Real.exp_add]
    simp only [L, neg_neg, Real.exp_log hv.1]
  change entranceReturnState y 1 ≤ y 1 * Real.exp (-(1 + k / 3) * L) ∧
    entranceReturnState y 3 ≤ y 3 * Real.exp (-(1 + 1 / k) * L) at H
  rw [he, he] at H
  rw [show -(k / 3) * L = -k * L / 3 by ring,
    show -(1 / k) * L = -L / k by ring] at H
  simpa only [mul_assoc] using H
