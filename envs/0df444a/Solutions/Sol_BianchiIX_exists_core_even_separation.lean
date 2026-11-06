-- Prove2me | solution 1 for BianchiIX.exists_core_even_separation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:11:54.221774+00:00
-- url     : https://prove2.me/submissions/74ec2bad-4a63-4c49-990c-19b543f23162

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_exists_coreReflection_paid_step
import Theorems.Thm_BianchiIX_exists_reference_two_taub_visit
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
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
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

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
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

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

private theorem BianchiIX.continuous_normalizedEuclideanDistance :
    Continuous (fun p : NormalizedState × NormalizedState => normalizedEuclideanDistance p.1 p.2) := by
  unfold normalizedEuclideanDistance
  fun_prop

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

private theorem BianchiIX.normalized_finiteVisit_neighborhood {x q : NormalizedState} {T ε : ℝ}
    (hdom : T ∈ normalizedMaxDomain x 0)
    (hclose : normalizedEuclideanDistance (normalizedMaxCurve x 0 T) q < ε) :
    ∀ᶠ y in 𝓝 x, T ∈ normalizedMaxDomain y 0 ∧
      normalizedEuclideanDistance (normalizedMaxCurve y 0 T) q < ε := by
  have hpair : ContinuousAt (fun y : NormalizedState => (y, T)) x := by fun_prop
  have hflow : ContinuousAt (fun y : NormalizedState => normalizedMaxCurve y 0 T) x :=
    ContinuousAt.comp (f := fun y : NormalizedState => (y, T))
      (normalizedMaxCurve_regular hdom).2.continuousAt hpair
  have hdist := continuous_normalizedEuclideanDistance.continuousAt.comp
    (hflow.prodMk (continuousAt_const (y := q)))
  exact (hpair.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hdom)).and
    (hdist.eventually (isOpen_Iio.mem_nhds hclose))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_core_two_taub_visit {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ ρ > 0, ρ ≤ 1 / 16 ∧ ∀ Y : CoreAngleState,
      |Y 0 - 2| ≤ ρ → |Y 1| ≤ ρ → |Y 2| ≤ ρ →
      T ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 ∧
        normalizedEuclideanDistance
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 T) (taubPoint 1) < ε := by
  obtain ⟨T, hT, hdom, hclose⟩ := exists_reference_two_taub_visit hε
  let Y₀ : CoreAngleState := ![2, 0, 0]
  have hx : fromProjectiveState (coreRadiusEntry Y₀) = referenceEntryState 2 := by
    unfold referenceEntryState
    rw [referencePulse_entry (by norm_num : (1 : ℝ) < 2)]
    rfl
  have hD : projectiveStateDenom (coreRadiusEntry Y₀) ≠ 0 := by
    have H := referencePulse_denom_pos 2 (-referenceHalfTime 2)
    rw [referencePulse_entry (by norm_num : (1 : ℝ) < 2)] at H
    exact H.ne'
  have hc := ((contDiffAt_fromProjectiveState 1 hD).comp Y₀
    (contDiffAt_coreRadiusEntry 1 (by norm_num [Y₀]))).continuousAt
  have he := hc.eventually (hx.symm ▸ normalized_finiteVisit_neighborhood hdom hclose)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let ρ := min (r / 2) (1 / 16)
  have hρ : 0 < ρ := lt_min (half_pos hr) (by norm_num)
  refine ⟨T, hT, ρ, hρ, min_le_right _ _, ?_⟩
  intro Y hk hu hw
  have hdist : dist Y Y₀ ≤ ρ := by
    apply (dist_pi_le_iff hρ.le).mpr
    intro i
    fin_cases i
    · simpa [Y₀, Real.dist_eq] using hk
    · simpa [Y₀, Real.dist_eq] using hu
    · simpa [Y₀, Real.dist_eq] using hw
  exact hball (lt_of_le_of_lt hdist (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_core_radius_separation_of_away {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ 1 / 16 ∧ ∀ Y : CoreAngleState,
      |Y 1| ≤ ρ → |Y 2| ≤ ρ →
      (∀ T > 0, T ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 →
        ε ≤ normalizedEuclideanDistance
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 T) (taubPoint 1)) →
      ρ < |Y 0 - 2| := by
  obtain ⟨T, hT, ρ, hρ, hρle, H⟩ := exists_core_two_taub_visit hε
  refine ⟨ρ, hρ, hρle, fun Y hu hw haway => ?_⟩
  by_contra! hk
  obtain ⟨hdom, hnear⟩ := H Y hk hu hw
  exact (not_lt_of_ge (haway T hT hdom)) hnear

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


/-- Finite actual prefixes exclude every positive even integer, with a length-independent error budget. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ρ ≤ 1 / 16 ∧ ∀ Y : CoreAngleState,
        0 < Y 1 → 0 < Y 2 → Y 1 + Y 2 ≤ δ / (1 + Y 0) → C * (Y 1 + Y 2) ≤ ρ / 4 →
        normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) →
        ∀ n : ℕ, 1 ≤ n → ρ / 2 < |Y 0 - 2 * n| := by
  obtain ⟨δ, hδ, hδmax, C, hC, Hstep⟩ := exists_coreReflection_paid_step
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  refine ⟨δ, hδ, hδmax, C, hC, ?_⟩
  intro ε hε
  obtain ⟨ρ, hρ, hρmax, Hsep⟩ := exists_core_radius_separation_of_away hε
  refine ⟨ρ, hρ, hρmax, ?_⟩
  intro Y hu hw hbudget hsmall haway n hn
  by_contra! hnear
  let G := coreReflectionState coreRadiusReturnTime
  let Z : ℕ → CoreAngleState := fun j => G^[j] Y
  let b : ℕ → ℝ := fun j => Z j 1 + Z j 2
  have hZ0 : Z 0 = Y := rfl
  have hZnext (j : ℕ) : Z (j + 1) = G (Z j) := Function.iterate_succ_apply' G j Y
  have hb0 : 0 < b 0 := add_pos hu hw
  have hsmall' : C * b 0 ≤ ρ / 4 := hsmall
  have hprefix : ∀ j, j ≤ n - 1 →
      (0 < Z j 1 ∧ 0 < Z j 2) ∧ b j ≤ b 0 ∧ Z j 0 ≤ Y 0 ∧
      |Z j 0 - (Y 0 - 2 * j)| ≤ C * (b 0 - b j) ∧
      normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry (Z j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⟨hu, hw⟩, le_rfl, le_rfl, ?_, haway⟩
      simp only [hZ0, Nat.cast_zero, mul_zero, sub_zero, sub_self, abs_zero, le_refl]
    | succ j ih =>
      intro hj
      obtain ⟨hpos, hb, hk, herr, ha⟩ := ih (by omega)
      have hbj : 0 ≤ b j := add_nonneg hpos.1.le hpos.2.le
      have hpaid : C * (b 0 - b j) ≤ ρ / 4 :=
        (mul_le_mul_of_nonneg_left (sub_le_self _ hbj) hC0).trans hsmall'
      have hnj : (j : ℝ) + 2 ≤ n := by exact_mod_cast (show j + 2 ≤ n by omega)
      have hguard : 63 / 16 ≤ Z j 0 := by
        have H1 := (abs_le.mp hnear).1
        have H2 := (abs_le.mp (herr.trans hpaid)).1
        linarith only [H1, H2, hnj, hρmax]
      have hentry : b j ≤ δ / (1 + Z j 0) :=
        (hb.trans hbudget).trans (div_le_div_of_nonneg_left hδ.le
          (by linarith only [hguard] : 0 < 1 + Z j 0) (by linarith only [hk]))
      obtain ⟨hcore, hT, horbit, hdrop, hwall, hphase⟩ := Hstep (Z j) hguard hpos.1 hpos.2 hentry
      have hbn : b (j + 1) ≤ b j := by
        change Z (j + 1) 1 + Z (j + 1) 2 ≤ _
        rw [hZnext]
        exact add_le_add (hwall 0).2 (hwall 1).2
      have hphase' : |Z (j + 1) 0 - (Z j 0 - 2)| ≤ C * (b j - b (j + 1)) := by
        simpa only [b, hZnext, G] using hphase
      have herror : |Z (j + 1) 0 - (Y 0 - 2 * (j + 1 : ℕ))| ≤ C * (b 0 - b (j + 1)) := by
        have heq : Z (j + 1) 0 - (Y 0 - 2 * (j + 1 : ℕ)) =
            (Z (j + 1) 0 - (Z j 0 - 2)) + (Z j 0 - (Y 0 - 2 * j)) := by
          push_cast
          ring
        rw [heq]
        exact ((abs_add_le _ _).trans (add_le_add hphase' herr)).trans_eq (by ring)
      refine ⟨?_, hbn.trans hb, ?_, herror, ?_⟩
      · rw [hZnext]
        exact ⟨(hwall 0).1, (hwall 1).1⟩
      · rw [hZnext]
        linarith only [hdrop.1, hk]
      · rw [hZnext]
        exact ha.coreReflection hcore hT horbit
  let m := n - 1
  obtain ⟨hpos, hb, _, herr, ha⟩ := hprefix m le_rfl
  have hm : (m : ℝ) + 1 = n := by exact_mod_cast (show m + 1 = n by dsimp [m]; omega)
  have hbm : 0 ≤ b m := add_nonneg hpos.1.le hpos.2.le
  have hpaid : C * (b 0 - b m) ≤ ρ / 4 :=
    (mul_le_mul_of_nonneg_left (sub_le_self _ hbm) hC0).trans hsmall'
  have hterminal : |Z m 0 - 2| ≤ ρ := by
    have H1 := abs_le.mp hnear
    have H2 := abs_le.mp (herr.trans hpaid)
    apply abs_le.mpr
    constructor <;> linarith only [H1.1, H1.2, H2.1, H2.2, hm, hρ]
  have hbr : b m ≤ ρ := by
    have H := mul_le_mul_of_nonneg_right hC hb0.le
    nlinarith only [H, hsmall', hb, hρ]
  have hu' : |Z m 1| ≤ ρ := by
    rw [abs_of_pos hpos.1]
    change Z m 1 + Z m 2 ≤ ρ at hbr
    linarith only [hbr, hpos.2]
  have hw' : |Z m 2| ≤ ρ := by
    rw [abs_of_pos hpos.2]
    change Z m 1 + Z m 2 ≤ ρ at hbr
    linarith only [hbr, hpos.1]
  have H := Hsep (Z m) hu' hw' (fun T hT hdom => ha T hT.le hdom 1)
  exact (not_lt_of_ge hterminal) H
