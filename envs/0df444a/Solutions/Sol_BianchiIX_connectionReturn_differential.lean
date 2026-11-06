-- Prove2me | solution 1 for BianchiIX.connectionReturn_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:42:17.784062+00:00
-- url     : https://prove2.me/submissions/0206accf-1e19-46f5-9c2c-63eb0456151f

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_toProjectiveState_fderiv_field
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

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
open Set

private theorem BianchiIX.projectiveGrowingWall_fderiv {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (v : NormalizedState) :
    fderiv ℝ projectiveGrowingWall x v = (fderiv ℝ toProjectiveState x v) 3 := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (toProjectiveState x)).comp x
    ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ projectiveGrowingWall x = _ from hd.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.projective_growing_event_differential {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hw : projectiveField (toProjectiveState (normalizedMaxCurve x t₀ t)) 3 ≠ 0)
    (v : NormalizedState) :
    let y := normalizedMaxCurve x t₀ t
    let ξ := fderiv ℝ toProjectiveState y (normalizedFlowDifferential x t₀ t v)
    fderiv ℝ toProjectiveState y (normalizedEventDifferential projectiveGrowingWall x t₀ t v) =
      ξ - (ξ 3 / projectiveField (toProjectiveState y) 3) • projectiveField (toProjectiveState y) := by
  dsimp only
  change fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)
    (normalizedFlowDifferential x t₀ t v +
      (-(fderiv ℝ projectiveGrowingWall (normalizedMaxCurve x t₀ t)
        (normalizedField (normalizedMaxCurve x t₀ t)))⁻¹ *
          fderiv ℝ projectiveGrowingWall (normalizedMaxCurve x t₀ t)
            (normalizedFlowDifferential x t₀ t v)) • normalizedField (normalizedMaxCurve x t₀ t)) = _
  rw [map_add, map_smul, projectiveGrowingWall_fderiv hA (normalizedField _),
    toProjectiveState_fderiv_field hA hc, projectiveGrowingWall_fderiv hA]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connection_entry_denom_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))⟩
  exact (connection_denom_bound (m := p 0) (v := 1) hu' (by norm_num)
    ⟨hw.1.le, hw.2.trans (by norm_num)⟩).2

end
end

/-- The canonical return derivative includes the variation of the actual arrival time. -/
theorem solution {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    let x := connectionInitialState p
    let T := connectionReturnTime p
    let y := normalizedMaxCurve x 0 T
    let ξ := fderiv ℝ toProjectiveState y (normalizedFlowDifferential x 0 T (fderiv ℝ connectionInitialState p v))
    fderiv ℝ connectionReturnTime p v = -(normalizedEventRate projectiveGrowingWall x 0 T)⁻¹ * ξ 3 ∧
      fderiv ℝ connectionReturnState p v =
        ξ - (ξ 3 / projectiveField (connectionReturnState p) 3) • projectiveField (connectionReturnState p) := by
  intro x T y ξ
  have H := connectionReturn_regular hμ hu hw
  have hvalid := H.1
  have htime := H.2.2.2.1
  have hstate := H.2.2.2.2.1
  have hA : 1 + y 0 ≠ 0 := ne_of_gt (hvalid.2.1 T ⟨hvalid.1.1.1.le, le_rfl⟩).2
  have hc : stateConstraint y = 1 := (normalizedMaxCurve_constraint hvalid.1.1.2.1).trans
    (fromProjectiveState_constraint (ne_of_gt (connection_entry_denom_pos hμ hu hw)))
  have hF : projectiveField (toProjectiveState y) 3 ≠ 0 := by
    intro heq
    have hr := hvalid.2.2.2
    rw [normalizedEventRate, projectiveGrowingWall_fderiv hA, toProjectiveState_fderiv_field hA hc] at hr
    change 0 < (1 + y 0) * projectiveField (toProjectiveState y) 3 at hr
    rw [heq, mul_zero] at hr
    exact lt_irrefl _ hr
  constructor
  · rw [htime.fderiv]
    change -(normalizedEventRate projectiveGrowingWall x 0 T)⁻¹ *
      fderiv ℝ projectiveGrowingWall y (normalizedFlowDifferential x 0 T (fderiv ℝ connectionInitialState p v)) = _
    rw [projectiveGrowingWall_fderiv hA]
  · rw [hstate.fderiv]
    exact projective_growing_event_differential hA hc hF (fderiv ℝ connectionInitialState p v)
