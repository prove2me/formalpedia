-- Prove2me | solution 1 for BianchiIX.connectionReturn_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:23:32.842219+00:00
-- url     : https://prove2.me/submissions/d39fe5d4-c1e1-4179-94aa-96c6c8bde1ae

import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_exists_growingWall_first_hit_two
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_connection_event_rate_pos
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

private theorem BianchiIX.contDiffAt_connectionInitialState (n : WithTop ℕ∞) {p : ConnectionParameters}
    (hD : projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) ≠ 0) :
    ContDiffAt ℝ n connectionInitialState p := by
  apply (contDiffAt_fromProjectiveState n hD).comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [connectionEntry] <;> fun_prop

private theorem BianchiIX.connection_entry_denom_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))⟩
  exact (connection_denom_bound (m := p 0) (v := 1) hu' (by norm_num)
    ⟨hw.1.le, hw.2.trans (by norm_num)⟩).2

/-- The canonical first hit is C2 in all three ordinary entry parameters, including U = 0. -/
theorem solution {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let x := connectionInitialState p
    let T := connectionReturnTime p
    connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p ∧
      HasFDerivAt connectionReturnTime
        ((normalizedEventTimeDifferential projectiveGrowingWall x 0 T).comp
          (fderiv ℝ connectionInitialState p)) p ∧
      HasFDerivAt connectionReturnState
        (((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveGrowingWall x 0 T)).comp
          (fderiv ℝ connectionInitialState p)) p ∧
      (∀ᶠ q in 𝓝 p, connectionReturnValid q) := by
  intro x T₀
  have hD := connection_entry_denom_pos hμ hu hw
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hinit : toProjectiveState (normalizedMaxCurve x 0 0) = connectionEntry (p 0) (p 1) (p 2) := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0 := by
    intro t ht
    exact ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      lt_of_lt_of_le (by positivity) (hprefix t ht).1⟩
  have hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveGrowingWall x 0 t := by
    intro t ht
    apply normalized_connection_event_rate_pos hc hμ (le_refl 0) ht.1
      (hreg 0 ⟨le_rfl, hT.le⟩).2 (hreg t ht).2 (hprefix t ht).2
    change 0 < toProjectiveState (normalizedMaxCurve x 0 0) 3
    simpa [hinit, connectionEntry] using hw.1
  obtain ⟨τ, hτ, hcτ, hcP, hdτ, hdP, hnear⟩ := exists_growingWall_first_hit_two hT hreg hrate hfirst.1.2.2
  have hcI := contDiffAt_connectionInitialState 2 (ne_of_gt hD)
  have hnear' := hcI.continuousAt.eventually hnear
  have heq : connectionReturnTime =ᶠ[𝓝 p] (fun q => τ (connectionInitialState q)) := by
    filter_upwards [hnear'] with q hq
    exact hq.1.csInf_eq
  have hT₀ : T₀ = T := heq.self_of_nhds.trans hτ
  have hnearValid : ∀ᶠ q in 𝓝 p, connectionReturnValid q := by
    filter_upwards [hnear', heq] with q hq htime
    dsimp only [connectionReturnValid]
    rw [htime]
    exact hq
  have hcTime : ContDiffAt ℝ 2 connectionReturnTime p :=
    (hcτ.comp p hcI).congr_of_eventuallyEq heq
  have heqP : connectionReturnState =ᶠ[𝓝 p]
      (fun q => toProjectiveState (normalizedMaxCurve (connectionInitialState q) 0 (τ (connectionInitialState q)))) := by
    filter_upwards [heq] with q hq
    simp only [connectionReturnState, hq]
  have hcState : ContDiffAt ℝ 2 connectionReturnState p :=
    (ContDiffAt.comp (g := fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
      (f := connectionInitialState) p hcP hcI).congr_of_eventuallyEq heqP
  have hdI := (hcI.differentiableAt (by norm_num)).hasFDerivAt
  have hdTime := (hdτ.comp p hdI).congr_of_eventuallyEq heq
  have hdState := (hdP.comp p hdI).congr_of_eventuallyEq heqP
  refine ⟨hnearValid.self_of_nhds, hcTime, hcState, ?_, ?_, hnearValid⟩
  · simpa only [hT₀] using hdTime
  · simpa only [hT₀] using hdState
