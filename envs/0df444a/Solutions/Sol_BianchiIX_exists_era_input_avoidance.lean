-- Prove2me | solution 1 for BianchiIX.exists_era_input_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:37:48.700324+00:00
-- url     : https://prove2.me/submissions/400e8d63-07ee-4630-8704-86d814bdf318

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_era_bounded_phase_estimates
import Theorems.Thm_BianchiIX_exists_era_input_estimates
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Theorems.Thm_BianchiIX_projectiveDenom_eq
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.projectiveReflection_denom (y : ProjectiveState) :
    projectiveStateDenom (projectiveReflection y) = projectiveStateDenom y := by
  dsimp [projectiveStateDenom, projectiveDenom, projectiveReflection, curvature]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fromProjectiveState_reflection (y : ProjectiveState) :
    fromProjectiveState (projectiveReflection y) = axisSwap (fromProjectiveState y) := by
  simp only [fromProjectiveState, projectiveReflection_denom]
  ext i
  fin_cases i <;> dsimp [projectiveReflection, axisSwap]
  all_goals ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_apply (i : Fin 6) (x : NormalizedState) :
    (axisFrame i).map x =
      ![x, axisCycle x, axisCycle (axisCycle x), axisSwap x,
        axisSwap (axisCycle x), axisSwap (axisCycle (axisCycle x))] i := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_nonneg (x y : NormalizedState) :
    0 ≤ normalizedEuclideanDistance x y := dist_nonneg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_sq (x y : NormalizedState) :
    normalizedEuclideanDistance x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp [normalizedEuclideanDistance, EuclideanSpace.dist_sq_eq, Real.dist_eq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_euclideanDistance (x y : NormalizedState) :
    normalizedEuclideanDistance (axisCycle x) (axisCycle y) = normalizedEuclideanDistance x y := by
  apply (sq_eq_sq₀ (normalizedEuclideanDistance_nonneg _ _)
    (normalizedEuclideanDistance_nonneg _ _)).mp
  rw [normalizedEuclideanDistance_sq, normalizedEuclideanDistance_sq]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [Fin.sum_univ_succ, axisCycle]
  ring_nf
  rw [hs]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_euclideanDistance (x y : NormalizedState) :
    normalizedEuclideanDistance (axisSwap x) (axisSwap y) = normalizedEuclideanDistance x y := by
  apply (sq_eq_sq₀ (normalizedEuclideanDistance_nonneg _ _)
    (normalizedEuclideanDistance_nonneg _ _)).mp
  rw [normalizedEuclideanDistance_sq, normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, axisSwap]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_euclideanDistance (i : Fin 6) (x y : NormalizedState) :
    normalizedEuclideanDistance ((axisFrame i).map x) ((axisFrame i).map y) =
      normalizedEuclideanDistance x y := by
  rw [axisFrame_apply, axisFrame_apply]
  fin_cases i <;> simp [axisCycle_euclideanDistance, axisSwap_euclideanDistance]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_taubPoint (i : Fin 3) : axisCycle (taubPoint i) = taubPoint (i + 2) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · change axisCycle ![-1, 0, 0, 0, 0] = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring
  · change axisCycle ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0] = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring_nf
    norm_num [hs]
  · change axisCycle ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring_nf
    norm_num [hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_taubPoint (i : Fin 3) : axisSwap (taubPoint i) = taubPoint (-i) := by
  fin_cases i
  · change axisSwap ![-1, 0, 0, 0, 0] = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring
  · change axisSwap ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring
  · change axisSwap ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_taubPoint_preimage (i : Fin 6) (j : Fin 3) :
    ∃ k : Fin 3, (axisFrame i).map (taubPoint k) = taubPoint j := by
  fin_cases i
  · exact ⟨j, by simp [axisFrame_apply]⟩
  · refine ⟨j + 1, ?_⟩
    simp only [axisFrame_apply, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨j + 2, ?_⟩
    simp only [axisFrame_apply, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨-j, ?_⟩
    simp [axisFrame_apply, axisSwap_taubPoint]
  · refine ⟨-j + 1, ?_⟩
    simp only [axisFrame_apply, axisSwap_taubPoint, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨-j + 2, ?_⟩
    simp only [axisFrame_apply, axisSwap_taubPoint, axisCycle_taubPoint]
    fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_away_taub {x : NormalizedState} {ε : ℝ}
    (haway : ∀ j, ε ≤ normalizedEuclideanDistance x (taubPoint j)) (i : Fin 6) :
    ∀ j, ε ≤ normalizedEuclideanDistance ((axisFrame i).map x) (taubPoint j) := by
  intro j
  obtain ⟨k, hk⟩ := axisFrame_taubPoint_preimage i j
  rw [← hk, axisFrame_euclideanDistance]
  exact haway k

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_of_upward_section {y : ProjectiveState}
    (hm : 1 ≤ y 0) (hv : y 2 = 1) :
    coreRadiusEntry (toCoreAngleState y) = y := by
  have he : coreEnergy (y 0) (y 2) = (y 0 - 1) ^ 2 + 1 := by
    simp only [coreEnergy, hv, one_pow]
  have hs : coreRadius (y 0) (y 2) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    rw [coreRadius, Real.sq_sqrt (by rw [he]; positivity), he]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (coreRadius (y 0) (y 2) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq (sub_nonneg.mpr hm)]
    ring
  · rfl
  · exact hv.symm
  · change y 2 * y 3 = y 3
    rw [hv, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRadiusReturnValid_denom_pos {Y : CoreAngleState} (H : coreRadiusReturnValid Y) :
    0 < projectiveStateDenom (coreRadiusEntry Y) := by
  have hzero := (H.2.1 0 ⟨le_rfl, H.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry Y) - 1) at hzero
  by_contra! hn
  have HD := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, HD]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.forward {ε s : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) (hs : 0 ≤ s) (hdom : s ∈ normalizedMaxDomain x 0) :
    normalizedTaubAvoidance ε (normalizedMaxCurve x 0 s) := by
  intro t ht htime i
  obtain ⟨hfull, heq⟩ := normalizedMaxCurve_restart (t := t + s) hdom (by simpa only [add_sub_cancel_right] using htime)
  simp only [add_sub_cancel_right] at heq
  rw [← heq]
  exact H _ (add_nonneg ht hs) hfull i

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.frame {ε : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) (i : Fin 6) :
    normalizedTaubAvoidance ε ((axisFrame i).map x) := by
  intro t ht hdom j
  rw [(axisFrame i).maxDomain] at hdom
  rw [(axisFrame i).maxCurve hdom]
  exact axisFrame_away_taub (H t ht hdom) i j

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreReflection_normalized_endpoint {Y : CoreAngleState}
    (hcore : coreRadiusReturnValid Y) (hT : 0 < coreReflectionTime Y)
    (hentry : coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
      projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    fromProjectiveState (coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y)) =
      axisSwap (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (coreReflectionTime Y)) := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreReflectionTime Y
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hcore).ne'
  have hd : T ∈ normalizedMaxDomain x 0 := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le
  have hA : 1 + normalizedMaxCurve x 0 T 0 ≠ 0 := by
    intro hz
    have H := congrArg (fun y : ProjectiveState => y 2) hentry
    change 1 = projectiveCoord (normalizedMaxCurve x 0 T 0) (normalizedMaxCurve x 0 T 4) at H
    simp only [projectiveCoord, hz, div_zero] at H
    norm_num at H
  rw [hentry, fromProjectiveState_reflection]
  exact congrArg axisSwap (fromProjectiveState_toProjectiveState hA ((normalizedMaxCurve_constraint hd).trans hc))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.coreReflection {ε : ℝ} {Y : CoreAngleState}
    (H : normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)))
    (hcore : coreRadiusReturnValid Y) (hT : 0 < coreReflectionTime Y)
    (hentry : coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
      projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    normalizedTaubAvoidance ε
      (fromProjectiveState (coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y))) := by
  rw [coreReflection_normalized_endpoint hcore hT hentry]
  have hc := fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hcore).ne'
  exact (H.forward hT.le (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le)).frame 3

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.unit_active_wall_clock_ne_zero {x : NormalizedState} (hv : toProjectiveState x 2 = 1) :
    1 + x 0 ≠ 0 := by
  intro hzero
  change projectiveCoord (x 0) (x 3) = 1 at hv
  simp only [projectiveCoord, hzero, div_zero] at hv
  norm_num at hv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.unit_active_wall_denom_pos {y : ProjectiveState} (hv : y 2 = 1)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 4) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 4) :
    0 < projectiveStateDenom y := by
  have hp : y 1 * (1 + y 3) ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + y 3 ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + y 3) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    norm_num at H
    exact H
  rw [projectiveStateDenom, projectiveDenom_eq, hv]
  nlinarith only [hp, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (1 - y 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.upward_core_normalized_reconstruction {x : NormalizedState}
    (hc : stateConstraint x = 1) (hv : toProjectiveState x 2 = 1)
    (hu : 0 ≤ toProjectiveState x 1 ∧ toProjectiveState x 1 ≤ 1 / 4)
    (hw : 0 ≤ toProjectiveState x 3 ∧ toProjectiveState x 3 ≤ 1 / 4)
    (htrans : 0 < fderiv ℝ projectiveActiveWall x (normalizedField x)) :
    let y := toProjectiveState x
    coreRadiusEntry ![coreRadius (y 0) (y 2), y 1, y 3] = y ∧
      fromProjectiveState (coreRadiusEntry ![coreRadius (y 0) (y 2), y 1, y 3]) = x := by
  intro y
  have hA := unit_active_wall_clock_ne_zero hv
  have hx := fromProjectiveState_toProjectiveState hA hc
  have hclock : 0 < 1 + x 0 := by
    simpa only [hx] using fromProjectiveState_clock_pos (unit_active_wall_denom_pos hv hu hw)
  rw [projectiveActiveWall_fderiv_field hA hc] at htrans
  have hvel : 0 < projectiveField y 2 := by
    by_contra! hn
    exact (not_le_of_gt htrans) (mul_nonpos_of_nonneg_of_nonpos hclock.le hn)
  change 0 < activeVelocity (y 0) (y 1) (y 2) (y 3) at hvel
  change y 2 = 1 at hv
  rw [activeVelocity, hv, mul_one] at hvel
  have hcoupling : 0 ≤ coupling (y 1) 1 (y 3) :=
    mul_nonneg hu.1 (by linarith only [hu.2, hw.1])
  have hm : 1 ≤ y 0 := by linarith only [hvel, hcoupling]
  have hcoords : toCoreAngleState y = ![coreRadius (y 0) (y 2), y 1, y 3] := by
    simp only [toCoreAngleState, hv, one_mul]
  have heq := coreRadiusEntry_of_upward_section hm hv
  rw [hcoords] at heq
  exact ⟨heq, (congrArg fromProjectiveState heq).trans hx⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreReturn_normalized_endpoint {Y : CoreAngleState} (H : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)) :
    fromProjectiveState (coreTailEntry (coreReturnState coreRadiusReturnTime Y)) =
      normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (coreRadiusReturnTime Y) := by
  have hA := (H.2.1 (coreRadiusReturnTime Y) ⟨H.1.1.1.le, le_rfl⟩).2
  rw [hchart]
  exact fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint H.1.1.2.1).trans
      (fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos H).ne'))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.coreReturn {ε : ℝ} {Y : CoreAngleState}
    (Ha : normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)))
    (H : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)) :
    normalizedTaubAvoidance ε (fromProjectiveState (coreTailEntry (coreReturnState coreRadiusReturnTime Y))) := by
  rw [coreReturn_normalized_endpoint H hchart]
  exact Ha.forward H.1.1.1.le H.1.1.2.1

end
end


/-- Every small selected-input era has a genuine upward physical endpoint and preserves Taub avoidance. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bstar m,
          let Y := eraNextState η J m p.2
          2 < Y 0 ∧ 0 < Y 1 ∧ 0 < Y 2 ∧ Y 1 + Y 2 ≤ p.1 ^ (4 / 3 : ℝ) ∧
          coreRadiusEntry Y = eraOutputState η J m p.2 ∧
          ∀ ε : ℝ, normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry p.2)) →
            normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) := by
  obtain ⟨δp, hδp, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨δa, hδa, _, HA⟩ := exists_era_input_estimates
  refine ⟨min δp δa, lt_min hδp hδa, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨a, ha, _, C, hC, Hp⟩ := HP η hη (hηδ.trans (min_le_left _ _)) J (by omega)
  obtain ⟨_, _, Ba, hBa, _, Ha⟩ := HA η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Br, hBr, hBrone, Hr⟩ := exists_retained_era_parameter_budget ha
    (le_trans zero_le_one hC) hσ hσone hσJ
  let Bstar := min Br (min Ba (1 / 4))
  have hBstar : 0 < Bstar := lt_min hBr (lt_min hBa (by norm_num))
  have hBBr : Bstar ≤ Br := min_le_left _ _
  have hBBa : Bstar ≤ Ba := (min_le_right _ _).trans (min_le_left _ _)
  have hBquarter : Bstar ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Bstar, hBstar, hBBr.trans_lt hBrone, ?_⟩
  intro m p hp Y
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨_, _, hU, hW, hsumOut, _⟩ := Ha m p ⟨⟨hB.1, hB.2.trans hBBa⟩, hm, hu, hw, hsum, hr⟩
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hr p.1 ⟨hB.1, hB.2.trans hBBr⟩
  have hcap : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBrX : p.1 * p.2 0 ≤ a :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hcap)
  have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ a / p.2 0 :=
    (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBrX)
  have hphase : (m : ℝ) + 1 + p.1 ^ σ ≤ p.2 0 / 2 ∧ p.2 0 / 2 ≤ (m : ℝ) + 2 - p.1 ^ σ := by
    constructor <;> linarith only [hr.1, hr.2]
  obtain ⟨_, _, _, _, _, _, _, hR, Hvalid, Hconn, _, hchart, Hfirst, Hactual, Hunit, Htrans, _⟩ :=
    Hp m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
      ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
      (hsum.trans hsmall) hphase
      ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)
  let Z := eraCoreExit m p.2
  let x := axisCycle (fromProjectiveState (coreTailEntry Z))
  let T := terminalNaturalTime η J Z
  have hlast := Hvalid m le_rfl
  have hlastEndpoint := coreReturn_normalized_endpoint hlast hchart
  have hc : stateConstraint x = 1 := by
    rw [show x = axisCycle (fromProjectiveState (coreTailEntry Z)) from rfl, axisCycle_constraint]
    change stateConstraint (fromProjectiveState (coreTailEntry
      (coreReturnState coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] p.2)))) = 1
    rw [hlastEndpoint]
    exact (normalizedMaxCurve_constraint hlast.1.1.2.1).trans
      (fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hlast).ne')
  have hsmallOut : Y 1 + Y 2 ≤ 1 / 4 := hsumOut.trans
    ((Real.rpow_le_self_of_le_one hB.1.le (hB.2.trans (hBBr.trans hBrone.le)) (by norm_num)).trans
      (hB.2.trans hBquarter))
  change terminalNaturalState η J Z 1 + terminalNaturalState η J Z 3 ≤ 1 / 4 at hsmallOut
  change 0 < terminalNaturalState η J Z 1 at hU
  change 0 < terminalNaturalState η J Z 3 at hW
  have hrec := upward_core_normalized_reconstruction
    ((normalizedMaxCurve_constraint Hfirst.1.2.1).trans hc)
    (by rw [Hactual]; exact Hunit)
    (by rw [Hactual]; exact ⟨hU.le, by linarith only [hsmallOut, hW]⟩)
    (by rw [Hactual]; exact ⟨hW.le, by linarith only [hsmallOut, hU]⟩) Htrans
  dsimp only at hrec
  rw [Hactual] at hrec
  change coreRadiusEntry Y = eraOutputState η J m p.2 ∧
    fromProjectiveState (coreRadiusEntry Y) = normalizedMaxCurve x 0 T at hrec
  refine ⟨hR, hU, hW, hsumOut, hrec.1, ?_⟩
  intro ε Ha
  have Hprefix : ∀ j ≤ m, normalizedTaubAvoidance ε
      (fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j] p.2))) := by
    intro j
    induction j with
    | zero => intro _; exact Ha
    | succ j ih =>
      intro hj
      obtain ⟨_, hT, horbit⟩ := Hconn j (by omega)
      rw [Function.iterate_succ_apply']
      exact (ih (by omega)).coreReflection (Hvalid j (by omega)) hT horbit
  have Hdown := (Hprefix m le_rfl).coreReturn hlast hchart
  have Hcycle : normalizedTaubAvoidance ε x := Hdown.frame 1
  rw [hrec.2]
  exact Hcycle.forward Hfirst.1.1.le Hfirst.1.2.1
