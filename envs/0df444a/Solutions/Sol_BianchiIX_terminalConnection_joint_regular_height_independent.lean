-- Prove2me | solution 1 for BianchiIX.terminalConnection_joint_regular_height_independent
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:59:21.568072+00:00
-- url     : https://prove2.me/submissions/48942b12-506f-4fbe-858a-a58cef8ec16f

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_coreTail_joint_regular_of_valid
import Theorems.Thm_BianchiIX_entranceReturn_existing_orbit
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_projectiveDenom_of_constraint
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_constraint (x : NormalizedState) : stateConstraint (axisCycle x) = stateConstraint x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  dsimp [stateConstraint, constraint, shearSq, curvature, axisCycle]
  ring_nf
  norm_num [hs]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_projective (m u v w : ℝ) :
    axisCycleDenom m u v w = projectiveDenom m u v w + 2 * m - 2 := by
  unfold axisCycleDenom projectiveDenom
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_projectiveCycleDenom (n : WithTop ℕ∞) : ContDiff ℝ n projectiveCycleDenom := by
  unfold projectiveCycleDenom axisCycleDenom curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCycle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hH : projectiveCycleDenom y ≠ 0) : ContDiffAt ℝ n projectiveCycle y := by
  have hD := (contDiff_projectiveCycleDenom n).contDiffAt (x := y)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun z : ProjectiveState => 1 - 4 * (z 0 + 1) / projectiveCycleDenom z) y
    fun_prop (disch := assumption)
  all_goals
    change ContDiffAt ℝ n (fun z : ProjectiveState => 4 * z _ / projectiveCycleDenom z) y
    fun_prop (disch := assumption)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveCycleDenom_eq (y : ProjectiveState) :
    projectiveCycleDenom y = projectiveStateDenom y + 2 * y 0 - 2 :=
  axisCycleDenom_projective _ _ _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_inverse_clock {y : ProjectiveState} (hD : projectiveStateDenom y ≠ 0) :
    1 + axisCycle (fromProjectiveState y) 0 =
      (6 / projectiveStateDenom y) * projectiveCycleDenom y / 4 := by
  have hr : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [projectiveCycleDenom_eq]
  dsimp only [axisCycle, fromProjectiveState, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toProjectiveState_axisCycle_inverse {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) (hH : projectiveCycleDenom y ≠ 0) :
    toProjectiveState (axisCycle (fromProjectiveState y)) = projectiveCycle y := by
  have hr : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have Hclock := axisCycle_inverse_clock hD
  have HH := projectiveCycleDenom_eq y
  ext i
  fin_cases i <;> change Real.sqrt 3 * axisCycle (fromProjectiveState y) _ /
    (1 + axisCycle (fromProjectiveState y) 0) = _ <;> rw [Hclock]
  · change Real.sqrt 3 * ((-Real.sqrt 3 * (6 / projectiveStateDenom y - 1) -
        6 / projectiveStateDenom y * y 0 / Real.sqrt 3) / 2) /
        (6 / projectiveStateDenom y * projectiveCycleDenom y / 4) =
      1 - 4 * (y 0 + 1) / projectiveCycleDenom y
    field_simp
    ring_nf
    rw [hr2]
    nlinarith only [HH]
  all_goals
    dsimp [axisCycle, fromProjectiveState, projectiveCycle]
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toProjectiveState_axisCycle {x : NormalizedState} (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1)
    (hH : projectiveCycleDenom (toProjectiveState x) ≠ 0) :
    toProjectiveState (axisCycle x) = projectiveCycle (toProjectiveState x) := by
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    have HD : projectiveStateDenom (toProjectiveState x) = 6 / (1 + x 0) := projectiveDenom_of_constraint hA hc
    rw [HD]
    exact div_ne_zero (by norm_num) hA
  have H := toProjectiveState_axisCycle_inverse hD hH
  rwa [fromProjectiveState_toProjectiveState hA hc] at H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

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

private theorem BianchiIX.coreTail_cycle_endpoint {h : ℝ} {Y : CoreAngleState} (HV : coreTailValid h Y)
    (hH : projectiveCycleDenom (coreTailState h Y) ≠ 0) :
    toProjectiveState (normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0
      (coreTailTime h Y)) = projectiveCycle (coreTailState h Y) := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime h Y
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have ht := HV.2.1 T ⟨HV.1.1.1.le, le_rfl⟩
  have hcycle : normalizedMaxCurve (axisCycle x) 0 T = axisCycle (normalizedMaxCurve x 0 T) :=
    NormalizedSymmetry.cycle.maxCurve ht.1
  change toProjectiveState (normalizedMaxCurve (axisCycle x) 0 T) = _
  rw [hcycle]
  exact toProjectiveState_axisCycle ht.2.ne'
    ((normalizedMaxCurve_forward_of_constraint hc HV.1.1.1.le).2.1) hH


/-- Locally the full physical arrival is C2 and independent of the intermediate height. -/
theorem solution {h : ℝ} {Y : CoreAngleState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hprefix : ∀ t ∈ Icc 0 (coreTailTime h Y),
      0 < 1 + normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t 0 ∧
      projectiveActiveWall (normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t) < 1) :
    let z := projectiveCycle (coreTailState h Y)
    7 / 4 < coreRadius (z 0) (z 2) → 1 < z 0 →
    (0 < z 1 ∧ z 1 < 1 / 10000) → (0 < z 2 ∧ z 2 < 1) →
    (0 < z 3 ∧ z 3 < 1 / 10000) →
    ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y) ∧
      ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y) ∧
      (∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
        terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
        terminalConnectionState p.1 p.2 = terminalConnectionState h p.2) := by
  intro z hk hm hu hv hw
  let p₀ : ℝ × CoreAngleState := (h, Y)
  let c : CoreAngleState → NormalizedState := fun Z => axisCycle (fromProjectiveState (coreTailEntry Z))
  let Z : ℝ × CoreAngleState → ProjectiveState := fun p => projectiveCycle (coreTailState p.1 p.2)
  have HT := coreTail_joint_regular_of_valid hR HV
  have HZ : ContDiffAt ℝ 2 Z p₀ := ContDiffAt.comp (g := projectiveCycle)
    (f := fun p : ℝ × CoreAngleState => coreTailState p.1 p.2) p₀
    (contDiffAt_projectiveCycle 2 hH.ne') HT.2.1
  have HE := entranceReturn_regular hk.le hm.le ⟨hu.1.le, hu.2.le⟩ hv ⟨hw.1.le, hw.2.le⟩
  have Htime : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => entranceReturnTime (Z p)) p₀ :=
    ContDiffAt.comp (g := entranceReturnTime) (f := Z) p₀ HE.2.1 HZ
  have Hstate : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => entranceReturnState (Z p)) p₀ :=
    ContDiffAt.comp (g := entranceReturnState) (f := Z) p₀ HE.2.2.1 HZ
  refine ⟨HT.1.add Htime, Hstate, ?_⟩
  have HZ₀ := continuousAt_pi.mp HZ.continuousAt 0
  have HZ₁ := continuousAt_pi.mp HZ.continuousAt 1
  have HZ₂ := continuousAt_pi.mp HZ.continuousAt 2
  have HZ₃ := continuousAt_pi.mp HZ.continuousAt 3
  have HK : ContinuousAt (fun p => coreRadius (Z p 0) (Z p 2)) p₀ :=
    (((HZ₀.sub_const 1).pow 2).add (HZ₂.pow 2)).sqrt
  have Hden : ContinuousAt (fun p : ℝ × CoreAngleState => projectiveCycleDenom (coreTailState p.1 p.2)) p₀ :=
    ((contDiff_projectiveCycleDenom 2).contDiffAt.comp p₀ HT.2.1).continuousAt
  have Hinputs : ∀ᶠ p in 𝓝 p₀,
      coreTailValid p.1 p.2 ∧ 0 < projectiveCycleDenom (coreTailState p.1 p.2) ∧
      7 / 4 ≤ coreRadius (Z p 0) (Z p 2) ∧ 1 ≤ Z p 0 ∧
      (0 ≤ Z p 1 ∧ Z p 1 ≤ 1 / 10000) ∧ (0 < Z p 2 ∧ Z p 2 < 1) ∧
      (0 ≤ Z p 3 ∧ Z p 3 ≤ 1 / 10000) := by
    filter_upwards [HT.2.2, Hden.eventually (isOpen_Ioi.mem_nhds hH),
      HK.eventually (isOpen_Ioi.mem_nhds hk), HZ₀.eventually (isOpen_Ioi.mem_nhds hm),
      HZ₁.eventually (isOpen_Ioo.mem_nhds hu), HZ₂.eventually (isOpen_Ioo.mem_nhds hv),
      HZ₃.eventually (isOpen_Ioo.mem_nhds hw)] with p hp hd hkp hmp hup hvp hwp
    exact ⟨hp, hd, hkp.le, hmp.le, ⟨hup.1.le, hup.2.le⟩, hvp, ⟨hwp.1.le, hwp.2.le⟩⟩
  have hc : ContDiffAt ℝ 2 c Y := axisCycleEquiv.contDiff.contDiffAt.comp Y
    ((contDiffAt_fromProjectiveState 2 (coreTailValid_denom_pos HV).ne').comp Y
      (contDiffAt_coreTailEntry 2 hR))
  have hconstraint : stateConstraint (c Y) = 1 := by
    rw [axisCycle_constraint]
    exact fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have Hprefix : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 p₀, ∀ t ∈ Icc 0 (coreTailTime p.1 p.2),
      0 < 1 + normalizedMaxCurve (c p.2) 0 t 0 ∧
      projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t) < 1 := by
    apply eventually_forall_movingInterval HT.1.continuousAt HV.1.1.1
    intro t ht
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint hconstraint 0 ht.1
    have hflow := (normalizedMaxCurve_regular hdom).2.continuousAt
    have hA : ContinuousAt (fun w : NormalizedState × ℝ => 1 + normalizedMaxCurve w.1 0 w.2 0) (c Y, t) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hV : ContinuousAt (fun w : NormalizedState × ℝ => projectiveActiveWall (normalizedMaxCurve w.1 0 w.2)) (c Y, t) :=
      ContinuousAt.comp (x := (c Y, t)) (g := projectiveActiveWall)
        (f := fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 0 w.2)
        (contDiffAt_projectiveActiveWall 1 (hprefix t ht).1.ne').continuousAt hflow
    have hparam : ContinuousAt (fun w : (ℝ × CoreAngleState) × ℝ => (c w.1.2, w.2)) (p₀, t) :=
      (ContinuousAt.comp (x := (p₀, t)) (g := c) (f := fun w : (ℝ × CoreAngleState) × ℝ => w.1.2)
        hc.continuousAt (continuousAt_snd.comp continuousAt_fst)).prodMk continuousAt_snd
    exact hparam.eventually ((hA.eventually (isOpen_Ioi.mem_nhds (hprefix t ht).1)).and
      (hV.eventually (isOpen_Iio.mem_nhds (hprefix t ht).2)))
  have Hphysical : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 p₀,
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (c p.2) 0 ∧
        projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t) = 1} (terminalConnectionTime p.1 p.2) ∧
      toProjectiveState (normalizedMaxCurve (c p.2) 0 (terminalConnectionTime p.1 p.2)) =
        terminalConnectionState p.1 p.2 := by
    filter_upwards [Hinputs, Hprefix] with p hp hpp
    have hcp : stateConstraint (c p.2) = 1 := by
      rw [axisCycle_constraint]
      exact fromProjectiveState_constraint (coreTailValid_denom_pos hp.1).ne'
    have HH := entranceReturn_existing_orbit hcp hp.1.1.1.1.le
      (coreTail_cycle_endpoint hp.1 hp.2.1.ne') hpp hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
      hp.2.2.2.2.2.1 hp.2.2.2.2.2.2
    exact ⟨HH.2.2.2.1, HH.2.2.2.2.2.2.1⟩
  have hfixed : ContinuousAt (fun p : ℝ × CoreAngleState => (h, p.2)) p₀ :=
    continuousAt_const.prodMk continuousAt_snd
  filter_upwards [Hphysical, hfixed.eventually Hphysical] with p hp hf
  have heq := hp.1.unique hf.1
  refine ⟨heq, hp.2.symm.trans ?_⟩
  rw [heq]
  exact hf.2
