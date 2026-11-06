-- Prove2me | solution 1 for BianchiIX.coreTail_reference_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:56:27.675522+00:00
-- url     : https://prove2.me/submissions/b958abd8-9140-4e4c-b359-ea3b6971f29c

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
import Theorems.Thm_BianchiIX_exists_activeWall_first_downward_hit_two
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referencePulse_height_exit
import Theorems.Thm_BianchiIX_referenceTail_normalized_segment
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceTail_active_hit {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    projectiveActiveWall (normalizedMaxCurve (referenceExitState k) 0 (referenceTailTime k η)) = η := by
  have H := referenceTail_normalized_segment hk hη
  have hD : 0 < projectiveStateDenom (![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState) := by
    rw [← referencePulse_height_exit (lt_trans zero_lt_one hk) ⟨hη.1, hη.2.trans hk⟩]
    exact referencePulse_denom_pos k _
  rw [H.2.1]
  unfold projectiveActiveWall
  rw [toProjectiveState_fromProjectiveState (ne_of_gt hD)]
  rfl

end
end

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

private theorem BianchiIX.coreTailEntry_reference {k : ℝ} (hk : 1 < k) :
    coreTailEntry ![k, 0, 0] = referencePulse k (referenceHalfTime k) := by
  rw [referencePulse_exit hk]
  rfl

/-- The finite tail has a canonical first-hit map with two derivatives near each boundary orbit. -/
theorem solution {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    coreTailTime η ![k, 0, 0] = referenceTailTime k η ∧
      coreTailState η ![k, 0, 0] = ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] ∧
      ContDiffAt ℝ 2 (coreTailTime η) ![k, 0, 0] ∧
      ContDiffAt ℝ 2 (coreTailState η) ![k, 0, 0] ∧
      (∀ᶠ Y in 𝓝 (![k, 0, 0] : CoreAngleState), coreTailValid η Y) := by
  let Y₀ : CoreAngleState := ![k, 0, 0]
  let c : CoreAngleState → NormalizedState := fun Y => fromProjectiveState (coreTailEntry Y)
  have hc₀ : c Y₀ = referenceExitState k := by
    dsimp only [c, Y₀]
    rw [coreTailEntry_reference hk]
    rfl
  have hD : 0 < projectiveStateDenom (coreTailEntry Y₀) := by
    rw [coreTailEntry_reference hk]
    exact referencePulse_denom_pos k _
  have hcc : ContDiffAt ℝ 2 c Y₀ :=
    (contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp Y₀ (contDiffAt_coreTailEntry 2 hk)
  have H := referenceTail_normalized_segment hk hη
  obtain ⟨τ, hτ, hcτ, hcP, _, hnear⟩ := exists_activeWall_first_downward_hit_two H.1
    (fun t ht => ⟨(H.2.2 t ht).1, (H.2.2 t ht).2.1⟩)
    (fun t ht => (H.2.2 t ht).2.2.1) (referenceTail_active_hit hk hη)
  have hsmall : ∀ᶠ x in 𝓝 (referenceExitState k), ∀ t ∈ Icc 0 (τ x),
      |toProjectiveState (normalizedMaxCurve x 0 t) 3| < 1 / 2 := by
    apply eventually_forall_movingInterval hcτ.continuousAt (by rw [hτ]; exact H.1)
    intro t ht
    rw [hτ] at ht
    have hreg := H.2.2 t ht
    have hf := (normalizedMaxCurve_regular hreg.1).2.continuousAt
    have hp : ContinuousAt (fun q : NormalizedState × ℝ =>
        toProjectiveState (normalizedMaxCurve q.1 0 q.2)) (referenceExitState k, t) :=
      ContinuousAt.comp (g := toProjectiveState) (f := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
        (contDiffAt_toProjectiveState 1 (ne_of_gt hreg.2.1)).continuousAt hf
    apply (continuousAt_pi.mp hp 3).abs.eventually (isOpen_Iio.mem_nhds _)
    change |toProjectiveState (normalizedMaxCurve (referenceExitState k) 0 t) 3| < 1 / 2
    rw [hreg.2.2.2, abs_zero]
    norm_num
  have hnear' := hcc.continuousAt.eventually (hc₀.symm ▸ hnear)
  have hsmall' := hcc.continuousAt.eventually (hc₀.symm ▸ hsmall)
  have heq : coreTailTime η =ᶠ[𝓝 Y₀] (fun Y => τ (c Y)) := by
    filter_upwards [hnear'] with Y hY
    exact hY.1.csInf_eq
  have hcTime : ContDiffAt ℝ 2 (coreTailTime η) Y₀ :=
    ((hc₀.symm ▸ hcτ).comp Y₀ hcc).congr_of_eventuallyEq heq
  have hcOut : ContDiffAt ℝ 2 (coreTailState η) Y₀ := by
    have hcomp : ContDiffAt ℝ 2 (fun Y => toProjectiveState (normalizedMaxCurve (c Y) 0 (τ (c Y)))) Y₀ :=
      (hc₀.symm ▸ hcP).comp Y₀ hcc
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [heq] with Y hY
    dsimp only [coreTailState, projectiveOriginalFlow]
    rw [hY]
  have htime : coreTailTime η Y₀ = referenceTailTime k η :=
    heq.self_of_nhds.trans ((congrArg τ hc₀).trans hτ)
  refine ⟨htime, ?_, hcTime, hcOut, ?_⟩
  · change toProjectiveState (normalizedMaxCurve (c Y₀) 0 (coreTailTime η Y₀)) = _
    rw [hc₀, htime, H.2.1]
    have hDout : 0 < projectiveStateDenom (![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState) := by
      rw [← referencePulse_height_exit (lt_trans zero_lt_one hk) ⟨hη.1, hη.2.trans hk⟩]
      exact referencePulse_denom_pos k _
    exact toProjectiveState_fromProjectiveState (ne_of_gt hDout)
  · filter_upwards [heq, hnear', hsmall'] with Y hY hfirst hsmallY
    dsimp only [coreTailValid]
    rw [hY]
    exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1, hfirst.2.2.2, hsmallY⟩
