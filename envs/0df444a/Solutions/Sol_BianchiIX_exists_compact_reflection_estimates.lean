-- Prove2me | solution 1 for BianchiIX.exists_compact_reflection_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:31:23.959353+00:00
-- url     : https://prove2.me/submissions/c0bd5b78-8c85-4906-aacf-efa5512e716e

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_compactConnection_actual_passage
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreTail_joint_regular_of_valid
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_compact_connection_cone
import Theorems.Thm_BianchiIX_exists_compact_connection_entrance_data
import Theorems.Thm_BianchiIX_exists_compact_connection_phase_bounds
import Theorems.Thm_BianchiIX_exists_compact_connection_return
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

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

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadiusEntry_reflected_exit {y : ProjectiveState} (hM : 1 < -y 0) (hW : y 3 = 1) :
    coreRadiusEntry ![phaseNorm (-y 0 - 1) 1, y 1, y 2] = projectiveReflection y := by
  have hs : phaseNorm (-y 0 - 1) 1 ^ 2 - 1 = (-y 0 - 1) ^ 2 := by
    rw [phaseNorm_sq]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (phaseNorm (-y 0 - 1) 1 ^ 2 - 1) = -y 0
    rw [hs, Real.sqrt_sq (by linarith only [hM])]
    ring
  · rfl
  · exact hW.symm
  · rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionEntry_coreExitParameters (Y : CoreAngleState) :
    connectionEntry (coreExitConnectionParameters Y 0) (coreExitConnectionParameters Y 1)
      (coreExitConnectionParameters Y 2) = coreTailEntry Y := by
  ext i
  fin_cases i <;> simp [connectionEntry, coreExitConnectionParameters, coreTailEntry, neg_sub]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionReturnState_coreExitParameters (Y : CoreAngleState) :
    connectionReturnState (coreExitConnectionParameters Y) =
      projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) := by
  unfold connectionReturnState connectionInitialState
  rw [connectionEntry_coreExitParameters]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.reflectionReturn_state_reconstruction {Y : CoreAngleState}
    (hm : 1 < -projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) 0)
    (hw : projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) 3 = 1) :
    coreRadiusEntry (reflectionReturnState Y) =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) := by
  unfold reflectionReturnState connectionReturnPhysicalState
  rw [connectionReturnState_coreExitParameters]
  exact coreRadiusEntry_reflected_exit hm hw

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.reflectionReturn_compact_eq {η : ℝ} {Y : CoreAngleState}
    (htail : coreTailValid η Y) (hD : 0 < projectiveStateDenom (compactConnectionEntry η Y))
    (hreturn : entranceReturnValid (compactConnectionEntry η Y)) :
    reflectionReturnTime Y = compactConnectionTime η Y ∧
      reflectionReturnState Y = compactConnectionPhysicalState η Y := by
  obtain ⟨hstate, hfirst⟩ := compactConnection_actual_passage htail hD hreturn
  let p := coreExitConnectionParameters Y
  have hx : connectionInitialState p = fromProjectiveState (coreTailEntry Y) := by
    dsimp only [connectionInitialState, p]
    rw [connectionEntry_coreExitParameters]
  have hdom (t : ℝ) (ht : 0 ≤ t) : t ∈ normalizedMaxDomain (connectionInitialState p) 0 := by
    rw [hx]
    exact normalizedMaxDomain_contains_Ici_of_constraint
      (fromProjectiveState_constraint (coreTailValid_denom_pos htail).ne') 0 ht
  have hfirst' : IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (connectionInitialState p) 0 ∧
      projectiveGrowingWall (normalizedMaxCurve (connectionInitialState p) 0 t) = 1}
      (compactConnectionTime η Y) := by
    refine ⟨⟨hfirst.1.1, hdom _ hfirst.1.1.le, ?_⟩, ?_⟩
    · rw [hx]
      exact hfirst.1.2
    · intro t ht
      apply hfirst.2
      refine ⟨ht.1, ?_⟩
      rw [hx] at ht
      exact ht.2.2
  have htime : reflectionReturnTime Y = compactConnectionTime η Y := hfirst'.csInf_eq
  have hs : compactConnectionState η Y = projectiveReflection (connectionReturnState p) := by
    rw [connectionReturnState, hx, show connectionReturnTime p = compactConnectionTime η Y from htime]
    exact hstate
  have hactive : compactConnectionState η Y 2 = 1 := hreturn.1.1.2.2
  refine ⟨htime, ?_⟩
  ext i
  fin_cases i
  · change phaseNorm (-connectionReturnState p 0 - 1) 1 =
      coreRadius (compactConnectionState η Y 0) (compactConnectionState η Y 2)
    rw [hactive, hs]
    rfl
  · exact (congrFun hs 1).symm
  · exact (congrFun hs 3).symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.reflectionReturn_compact_eventuallyEq {η : ℝ} {Y : CoreAngleState}
    (hnear : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z ∧
      0 < projectiveStateDenom (compactConnectionEntry η Z) ∧
      entranceReturnValid (compactConnectionEntry η Z)) :
    reflectionReturnTime =ᶠ[𝓝 Y] compactConnectionTime η ∧
      reflectionReturnState =ᶠ[𝓝 Y] compactConnectionPhysicalState η := by
  exact ⟨hnear.mono fun _ h => (reflectionReturn_compact_eq h.1 h.2.1 h.2.2).1,
    hnear.mono fun _ h => (reflectionReturn_compact_eq h.1 h.2.1 h.2.2).2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_compactConnectionPhysicalState {η : ℝ} {Y : CoreAngleState}
    (hs : ContDiffAt ℝ 2 (compactConnectionState η) Y)
    (ha : 0 < compactConnectionState η Y 2) :
    ContDiffAt ℝ 2 (compactConnectionPhysicalState η) Y := by
  have hp := (contDiffAt_toCoreAngleState 2 ha).comp Y hs
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_pi.mp hp 0
  · exact contDiffAt_pi.mp hs 1
  · exact contDiffAt_pi.mp hs 3

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_compact_reflection_regular {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      (reflectionReturnTime =ᶠ[𝓝 Y] compactConnectionTime η) ∧
        (reflectionReturnState =ᶠ[𝓝 Y] compactConnectionPhysicalState η) ∧
        ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_connection_entrance_data
    (δ := 1 / 10000) (by norm_num) hη
  refine ⟨ε, hε, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, ht, he, hr, hm, hU, hV, hW, _, _⟩ := H Y hk hu hw
  have hR : 1 < Y 0 := by linarith only [hk.1]
  have hv : 0 < compactConnectionEntry η Y 2 ∧ compactConnectionEntry η Y 2 < 1 :=
    ⟨hV.1, by linarith only [hV.2]⟩
  have hw' : 0 ≤ compactConnectionEntry η Y 3 ∧ compactConnectionEntry η Y 3 ≤ 1 / 10000 := by
    rw [hW]
    exact ⟨hη.1.le, hη.2⟩
  have HR := entranceReturn_regular hr.1 hm ⟨hU.1.le, hU.2⟩ hv hw'
  have hD := entrance_initial_denom_pos hr.1 hm ⟨hU.1.le, hU.2⟩ hv hw'
  have htailNear : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (coreTail_joint_regular_of_valid hR htail).2.2
  have hreturnNear : ∀ᶠ Z in 𝓝 Y, entranceReturnValid (compactConnectionEntry η Z) :=
    he.continuousAt.eventually HR.2.2.2.2.2
  have hdenNear : ∀ᶠ Z in 𝓝 Y, 0 < projectiveStateDenom (compactConnectionEntry η Z) :=
    (continuous_projectiveStateDenom.continuousAt.comp he.continuousAt).eventually
      (isOpen_Ioi.mem_nhds hD)
  have hnear : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z ∧
      0 < projectiveStateDenom (compactConnectionEntry η Z) ∧
      entranceReturnValid (compactConnectionEntry η Z) := by
    filter_upwards [htailNear, hdenNear, hreturnNear] with Z htZ hdZ hrZ
    exact ⟨htZ, hdZ, hrZ⟩
  obtain ⟨heqT, heqF⟩ := reflectionReturn_compact_eventuallyEq hnear
  have htime : ContDiffAt ℝ 2 (compactConnectionTime η) Y := (HR.2.1.comp Y he).add ht
  have hstate : ContDiffAt ℝ 2 (compactConnectionState η) Y := HR.2.2.1.comp Y he
  have hactive : compactConnectionState η Y 2 = 1 := HR.1.1.1.2.2
  have hphysical := contDiffAt_compactConnectionPhysicalState hstate (by rw [hactive]; norm_num)
  exact ⟨heqT, heqF, htime.congr_of_eventuallyEq heqT, hphysical.congr_of_eventuallyEq heqF⟩

end
end

private theorem BianchiIX.compactConnectionPhysicalState_differential {η : ℝ} {Y : CoreAngleState}
    (hs : DifferentiableAt ℝ (compactConnectionState η) Y)
    (hf : DifferentiableAt ℝ (compactConnectionPhysicalState η) Y) (v : CoreAngleState) :
    fderiv ℝ (compactConnectionPhysicalState η) Y v =
      ![fderiv ℝ (compactConnectionPhase η) Y v,
        fderiv ℝ (compactConnectionState η) Y v 1, fderiv ℝ (compactConnectionState η) Y v 3] := by
  ext i
  fin_cases i
  · exact (congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) (fderiv_apply hf 0)).symm
  · have heq : (fun Z => compactConnectionPhysicalState η Z 1) =
        (fun Z => compactConnectionState η Z 1) := rfl
    have H := congrArg (fun f : CoreAngleState → ℝ => fderiv ℝ f Y) heq
    rw [fderiv_apply hf 1, fderiv_apply hs 1] at H
    exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H
  · have heq : (fun Z => compactConnectionPhysicalState η Z 2) =
        (fun Z => compactConnectionState η Z 3) := rfl
    have H := congrArg (fun f : CoreAngleState → ℝ => fderiv ℝ f Y) heq
    rw [fderiv_apply hf 2, fderiv_apply hs 3] at H
    exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H


/-- Compact reflection bounds belong to the canonical next-wall return, without an auxiliary tail-height parameter. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨δp, hδp, hδsmall, Hp⟩ := exists_compact_connection_phase_bounds
  obtain ⟨δc, hδc, _, Hc⟩ := exists_compact_connection_cone
  let η := min δp δc
  have hη : 0 < η ∧ η ≤ 1 / 10000 := ⟨lt_min hδp hδc, (min_le_left _ _).trans hδsmall⟩
  obtain ⟨εp, hεp, P, hP, HP⟩ := Hp η ⟨hη.1, min_le_left _ _⟩
  obtain ⟨εc, hεc, Q, hQ, HC⟩ := Hc η ⟨hη.1, min_le_right _ _⟩
  obtain ⟨εr, hεr, _, _, HR⟩ := exists_compact_connection_return hη
  obtain ⟨εg, hεg, HG⟩ := exists_compact_reflection_regular hη
  let ε := min εr (min εg (min εp (min εc (1 / 2))))
  have hε : 0 < ε := lt_min hεr (lt_min hεg (lt_min hεp (lt_min hεc (by norm_num))))
  have hεr' : ε ≤ εr := min_le_left _ _
  have hεg' : ε ≤ εg := (min_le_right _ _).trans (min_le_left _ _)
  have hεp' : ε ≤ εp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc' : ε ≤ εc := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let C := max (6 * (P + 1)) (12 * Q)
  have hPC : 6 * (P + 1) ≤ C := le_max_left _ _
  have hQC : 12 * Q ≤ C := le_max_right _ _
  refine ⟨ε, hε, C, lt_of_lt_of_le (by positivity : 0 < 6 * (P + 1)) hPC, ?_⟩
  intro Y hk hu hw
  obtain ⟨heqT, heqF, ht, hF⟩ := HG Y hk
    ⟨hu.1, hu.2.trans hεg'⟩ ⟨hw.1, hw.2.trans hεg'⟩
  obtain ⟨_, _, _, hs, hactual, hfirst, hm, _, hU, hW⟩ := HR Y hk
    ⟨hu.1, hu.2.trans hεr'⟩ ⟨hw.1, hw.2.trans hεr'⟩
  obtain ⟨_, _, _, hval, _⟩ := HP Y hk
    ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  obtain ⟨_, _, _, _, _, _, hfactor, hcone⟩ := HC Y hk
    ⟨hu.1, hu.2.trans hεc'⟩ ⟨hw.1, hw.2.trans hεc'⟩
  have hk0 : 0 < Y 0 := by linarith only [hk.1]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hb1 : Y 1 + Y 2 ≤ 1 := by linarith only [hu.2.trans hεhalf, hw.2.trans hεhalf]
  have hval' : |compactConnectionPhase η Y - (Y 0 - 2)| ≤ (P + 1) * (Y 1 + Y 2) := by
    have hsmall : 2 * Y 1 / Y 0 ≤ Y 1 := (div_le_iff₀ hk0).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hk.1 hu.1.le, hu.1.le])
    have hsplit : compactConnectionPhase η Y - (Y 0 - 2) =
        (compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0) - 2 * Y 1 / Y 0 := by ring
    have H := (abs_sub (compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0)
      (2 * Y 1 / Y 0)).trans (add_le_add hval le_rfl)
    rw [← hsplit, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hu.1.le) hk0.le)] at H
    have hsq : (Y 1 + Y 2) ^ 2 ≤ Y 1 + Y 2 := by nlinarith only [hb, hb1]
    nlinarith only [H, hsmall, mul_le_mul_of_nonneg_left hsq hP.le, hw.1.le]
  refine ⟨?_, ?_, ht, hF, ?_, ?_, ?_⟩
  · rw [heqT.self_of_nhds]
    exact hfirst
  · apply reflectionReturn_state_reconstruction
    · rw [heqT.self_of_nhds]
      rw [hactual] at hm
      exact hm
    · rw [heqT.self_of_nhds]
      exact hfirst.1.2
  · rw [heqF.self_of_nhds]
    change |compactConnectionPhase η Y - (Y 0 - 2)| ≤ _
    apply hval'.trans
    apply (le_div_iff₀ hk0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hk.2 (mul_nonneg (by linarith only [hP] : 0 ≤ P + 1) hb),
      mul_le_mul_of_nonneg_right hPC hb]
  · intro i
    rw [heqF.self_of_nhds]
    fin_cases i
    · exact ⟨hU.1, hU.2.2⟩
    · exact ⟨hW.1, hW.2.2⟩
  · intro v hv0 hv1 hv2 d
    obtain ⟨hr, herr, hc1, hc2⟩ := hcone v hv0 hv1 hv2
    have hd := compactConnectionPhysicalState_differential (hs.differentiableAt (by norm_num))
      ((hF.congr_of_eventuallyEq heqF.symm).differentiableAt (by norm_num)) v
    have heqd : d = ![fderiv ℝ (compactConnectionPhase η) Y v,
        fderiv ℝ (compactConnectionState η) Y v 1, fderiv ℝ (compactConnectionState η) Y v 3] :=
      (congrArg (fun L : CoreAngleState →L[ℝ] CoreAngleState => L v) heqF.fderiv_eq).trans hd
    rw [heqd]
    refine ⟨hr, herr.trans ?_, ?_⟩
    · have hroot : Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2) ≤ 2 * Real.sqrt (Y 1 + Y 2) := by
        have hsu : Real.sqrt (Y 1) ≤ Real.sqrt (Y 1 + Y 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_right hw.1.le)
        have hsw : Real.sqrt (Y 2) ≤ Real.sqrt (Y 1 + Y 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_left hu.1.le)
        have hw1 : Y 2 ≤ 1 := by linarith only [hw.2.trans hεhalf]
        nlinarith only [hsu, hsw, mul_le_mul_of_nonneg_right hw1 (Real.sqrt_nonneg (Y 2))]
      apply (mul_le_mul_of_nonneg_left hroot hQ.le).trans
      apply (le_div_iff₀ hk0).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hk.2 (by positivity : 0 ≤ 2 * Q * Real.sqrt (Y 1 + Y 2)),
        mul_le_mul_of_nonneg_right hQC (Real.sqrt_nonneg (Y 1 + Y 2))]
    · intro i
      rw [heqF.self_of_nhds]
      have hfac : Q * (Y 1 + Y 2) ^ (2 / 9 : ℝ) ≤ 1 := by linarith only [hfactor]
      have hbound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfac (Real.sqrt_nonneg (compactConnectionPhysicalState η Y i.succ)))
        (show 0 ≤ fderiv ℝ (compactConnectionPhase η) Y v by linarith only [hr])
      simp only [one_mul] at hbound
      fin_cases i
      · exact hc1.trans hbound
      · exact hc2.trans hbound
