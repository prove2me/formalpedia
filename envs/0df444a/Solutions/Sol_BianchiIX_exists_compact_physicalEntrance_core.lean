-- Prove2me | solution 1 for BianchiIX.exists_compact_physicalEntrance_core
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:09:20.626418+00:00
-- url     : https://prove2.me/submissions/0ee9aa57-d2c0-44f2-96d3-c7be264560d1

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_exists_compact_smooth_neighborhood
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_referenceEntrance_return
import Theorems.Thm_BianchiIX_referencePulse_active_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_energy
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_height_exit
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.normalizedEuclideanDistance_nonneg (x y : NormalizedState) :
    0 ≤ normalizedEuclideanDistance x y := dist_nonneg

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referencePulse_height_entry {k v : ℝ} (hk : 0 < k) (hv : 0 < v ∧ v < k) :
    referencePulse k (-referenceHeightTime k v) = referenceEntranceState k v := by
  have H := referencePulse_height_exit hk hv
  have HM := congrFun H 0
  have HV := congrFun H 2
  change 1 - k * Real.tanh (k * referenceHeightTime k v) = 1 - Real.sqrt (k ^ 2 - v ^ 2) at HM
  change k / Real.cosh (k * referenceHeightTime k v) = v at HV
  ext i
  fin_cases i
  · dsimp [referencePulse, referenceEntranceState]
    rw [mul_neg, Real.tanh_neg]
    linarith only [HM]
  · rfl
  · change k / Real.cosh (k * (-referenceHeightTime k v)) = v
    rw [mul_neg, Real.cosh_neg]
    exact HV
  · rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceEntrance_radius {k v : ℝ} (hk : 0 < k) (hv : 0 < v ∧ v < k) :
    coreRadius (referenceEntranceState k v 0) (referenceEntranceState k v 2) = k := by
  rw [← referencePulse_height_entry hk hv, coreRadius, referencePulse_energy, Real.sqrt_sq hk.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.continuous_referenceEntranceState :
    Continuous (fun p : ℝ × ℝ => referenceEntranceState p.1 p.2) := by
  unfold referenceEntranceState
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedState_norm_sub_le_euclidean (x y : NormalizedState) :
    ‖x - y‖ ≤ normalizedEuclideanDistance x y := by
  apply (pi_norm_le_iff_of_nonneg (normalizedEuclideanDistance_nonneg x y)).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.dist_eq, normalizedEuclideanDistance] using
    PiLp.dist_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 5)) (WithLp.toLp 2 y) i

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.physicalEntranceData_reference {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    physicalEntranceData (fromProjectiveState (referenceEntranceState k v)) =
      (referenceShiftClock k (-referenceHeightTime k v) (-referenceHalfTime k),
        referencePulse k (-referenceHalfTime k),
        fromProjectiveState (referencePulse k (-referenceHalfTime k)), k) := by
  have hD : 0 < projectiveStateDenom (referenceEntranceState k v) := by
    simp [referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
    positivity
  obtain ⟨ht, hP⟩ := referenceEntrance_return (k := k) (by linarith only [hk]) hv
  simp only [physicalEntranceData, toProjectiveState_fromProjectiveState hD.ne', ht, hP]
  have hR : coreRadius (referencePulse k (-referenceHalfTime k) 0) (referencePulse k (-referenceHalfTime k) 2) = k := by
    rw [coreRadius, referencePulse_energy, Real.sqrt_sq (by linarith only [hk])]
  rw [hR]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.physicalEntranceData_reference_germ {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    ∀ᶠ x in 𝓝 (fromProjectiveState (referenceEntranceState k v)),
      (0 < 1 + x 0 ∧ entranceReturnValid (toProjectiveState x)) ∧
        ContDiffAt ℝ 2 physicalEntranceData x := by
  let q := referenceEntranceState k v
  let z := fromProjectiveState q
  have hD : 0 < projectiveStateDenom q := by
    simp [q, referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
    positivity
  have hA : 0 < 1 + z 0 := fromProjectiveState_clock_pos hD
  have he : toProjectiveState z = q := toProjectiveState_fromProjectiveState hD.ne'
  have hqR : 7 / 4 ≤ coreRadius (q 0) (q 2) := by
    rw [referenceEntrance_radius (by linarith only [hk]) ⟨hv.1, by linarith only [hk, hv.2]⟩]
    linarith only [hk]
  have hreg := entranceReturn_regular hqR
    (show 1 ≤ q 0 from le_add_of_nonneg_right (Real.sqrt_nonneg _))
    (by dsimp [q, referenceEntranceState]; norm_num) hv (by dsimp [q, referenceEntranceState]; norm_num)
  have hq := contDiffAt_toProjectiveState 2 hA.ne'
  have hT : ContDiffAt ℝ 2 (fun x => entranceReturnTime (toProjectiveState x)) z :=
    (he.symm ▸ hreg.2.1).comp z hq
  have hP : ContDiffAt ℝ 2 (fun x => entranceReturnState (toProjectiveState x)) z :=
    (he.symm ▸ hreg.2.2.1).comp z hq
  have hval : entranceReturnState (toProjectiveState z) = referencePulse k (-referenceHalfTime k) := by
    rw [he]
    exact (referenceEntrance_return (by linarith only [hk]) hv).2
  have hPD : 0 < projectiveStateDenom (entranceReturnState (toProjectiveState z)) := by
    rw [hval]
    exact referencePulse_denom_pos _ _
  have hPV : 0 < entranceReturnState (toProjectiveState z) 2 := by
    rw [hval]
    exact referencePulse_active_pos (by linarith only [hk]) _
  have hX := (contDiffAt_fromProjectiveState 2 hPD.ne').comp z hP
  have hR := contDiffAt_pi.mp ((contDiffAt_toCoreAngleState 2 hPV).comp z hP) 0
  have hF : ContDiffAt ℝ 2 physicalEntranceData z := hT.prodMk (hP.prodMk (hX.prodMk hR))
  have hnear := hq.continuousAt.eventually (he.symm ▸ hreg.2.2.2.2.2)
  have hnearA : ∀ᶠ x in 𝓝 z, 0 < 1 + x 0 :=
    (show Continuous (fun x : NormalizedState => 1 + x 0) from
      continuous_const.add (continuous_apply (0 : Fin 5))).continuousAt.eventually (isOpen_Ioi.mem_nhds hA)
  filter_upwards [hnearA, hnear, hF.eventually (by norm_num)] with x hx hvx hFx
  exact ⟨⟨hx, hvx⟩, hFx⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_compact_physicalEntrance_data {K a : ℝ} (ha : 0 < a) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ k ∈ Icc 2 K, ∀ v ∈ Icc a (1 / 2),
      ∀ x : NormalizedState,
        normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x ≤ δ →
        (0 < 1 + x 0 ∧ entranceReturnValid (toProjectiveState x)) ∧
          ContDiffAt ℝ 2 physicalEntranceData x ∧ ‖physicalEntranceData x‖ ≤ C ∧
          ‖physicalEntranceData x - physicalEntranceData (fromProjectiveState (referenceEntranceState k v))‖ ≤
            C * normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x := by
  let Q : ℝ × ℝ → NormalizedState := fun p => fromProjectiveState (referenceEntranceState p.1 p.2)
  let B : Set (ℝ × ℝ) := Icc 2 K ×ˢ Icc a (1 / 2)
  have hQ : ContinuousOn Q B := by
    intro p hp
    have hD : 0 < projectiveStateDenom (referenceEntranceState p.1 p.2) := by
      simp [referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
      positivity
    exact ((contDiffAt_fromProjectiveState 1 hD.ne').continuousAt.comp
      (f := fun p : ℝ × ℝ => referenceEntranceState p.1 p.2)
      continuous_referenceEntranceState.continuousAt).continuousWithinAt
  have hS : IsCompact (Q '' B) := (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hQ
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_smooth_neighborhood hS
    (P := fun x => 0 < 1 + x 0 ∧ entranceReturnValid (toProjectiveState x))
    (f := physicalEntranceData) (by
      rintro z ⟨⟨k, v⟩, ⟨hk, hv⟩, rfl⟩
      exact physicalEntranceData_reference_germ hk.1 ⟨ha.trans_le hv.1, by linarith only [hv.2]⟩)
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro k hk v hv x hx
  let z := fromProjectiveState (referenceEntranceState k v)
  have hnorm : ‖x - z‖ ≤ normalizedEuclideanDistance z x := by
    rw [norm_sub_rev]
    exact normalizedState_norm_sub_le_euclidean z x
  have HH := H z ⟨(k, v), ⟨hk, hv⟩, rfl⟩ x (hnorm.trans hx)
  exact ⟨HH.1, HH.2.1, HH.2.2.1,
    HH.2.2.2.trans (mul_le_mul_of_nonneg_left hnorm (by linarith only [hC]))⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceCoreWallFloor_pos (K : ℝ) : 0 < referenceCoreWallFloor K := by
  unfold referenceCoreWallFloor
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceCore_endpoint_bounds {k K : ℝ} (hk : 2 ≤ k ∧ k ≤ K) :
    2 ≤ referencePulse k (-referenceHalfTime k) 0 ∧
      2 * referenceCoreWallFloor K ≤ fromProjectiveState (referencePulse k (-referenceHalfTime k)) 3 := by
  have hk1 : 1 < k := by linarith only [hk.1]
  have hroot : Real.sqrt (k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt (by nlinarith only [hk.1])
  have hr0 := Real.sqrt_nonneg (k ^ 2 - 1)
  have hrlo : 1 ≤ Real.sqrt (k ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith only [hk.1])
  have hrhi : Real.sqrt (k ^ 2 - 1) ≤ k := by nlinarith only [hroot, hr0, hk.1]
  have hm : 0 ≤ 1 + Real.sqrt (k ^ 2 - 1) := by positivity
  have hmK : 1 + Real.sqrt (k ^ 2 - 1) ≤ 1 + K := by linarith only [hrhi, hk.2]
  have hden : 4 + (1 + Real.sqrt (k ^ 2 - 1)) ^ 2 ≤ 4 + (1 + K) ^ 2 := by
    nlinarith only [(sq_le_sq₀ hm (hm.trans hmK)).mpr hmK]
  have hrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrt0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [referencePulse_entry hk1]
  refine ⟨by change 2 ≤ 1 + Real.sqrt (k ^ 2 - 1); linarith only [hrlo], ?_⟩
  have he : fromProjectiveState (![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0] : ProjectiveState) 3 =
      2 * Real.sqrt 3 / (4 + (1 + Real.sqrt (k ^ 2 - 1)) ^ 2) := by
    simp [fromProjectiveState, projectiveStateDenom, projectiveDenom, curvature]
    field_simp
    nlinarith only [hrt]
  rw [he]
  have H := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrt0.le)
    (by positivity : 0 < 4 + (1 + Real.sqrt (k ^ 2 - 1)) ^ 2) hden
  simpa only [referenceCoreWallFloor, mul_div_assoc] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.physicalEntranceData_actual {x : NormalizedState}
    (hc : stateConstraint x = 1) (hA : 0 < 1 + x 0)
    (hv : entranceReturnValid (toProjectiveState x)) :
    let T := (physicalEntranceData x).1
    let X := normalizedMaxCurve x 0 T
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
      (physicalEntranceData x).2.1 = toProjectiveState X ∧
      (physicalEntranceData x).2.2.1 = X ∧
      (physicalEntranceData x).2.1 2 = 1 ∧ 0 < 1 + X 0 ∧
      HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve x 0 t))
        (normalizedEventRate projectiveActiveWall x 0 T) T ∧
      0 < normalizedEventRate projectiveActiveWall x 0 T := by
  intro T X
  have hback := fromProjectiveState_toProjectiveState hA.ne' hc
  have H := hv
  dsimp only [entranceReturnValid] at H
  rw [hback] at H
  change IsLeast _ T ∧ _ at H
  have htime : T ∈ Icc 0 T := ⟨H.1.1.1.le, le_rfl⟩
  have hAX : 0 < 1 + X 0 := (H.2.1 T htime).2
  have hcX : stateConstraint X = 1 := (normalizedMaxCurve_constraint H.1.1.2.1).trans hc
  have hP : (physicalEntranceData x).2.1 = toProjectiveState X := by
    change toProjectiveState (normalizedMaxCurve (fromProjectiveState (toProjectiveState x)) 0 T) = _
    rw [hback]
  have hphys : (physicalEntranceData x).2.2.1 = X := by
    change fromProjectiveState ((physicalEntranceData x).2.1) = X
    rw [hP, fromProjectiveState_toProjectiveState hAX.ne' hcX]
  refine ⟨H.1, hP, hphys, ?_, hAX, ?_, H.2.2.2 T htime⟩
  · rw [hP]
    exact H.1.1.2.2
  · exact ((contDiffAt_projectiveActiveWall 1 hAX.ne').differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T
      (hasDerivAt_normalizedMaxCurve H.1.1.2.1)

end
end


/-- The compact reference family controls the genuine physical first core, with a positive wall floor. -/
theorem solution {K a : ℝ} (ha : 0 < a) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ k ∈ Icc 2 K, ∀ v ∈ Icc a (1 / 2),
      ∀ x : NormalizedState, stateConstraint x = 1 →
        normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x ≤ δ →
        let T := (physicalEntranceData x).1
        let X := normalizedMaxCurve x 0 T
        let Y := toProjectiveState X
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
          T ≤ C ∧ Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
          |coreRadius (Y 0) (Y 2) - k| ≤
            C * normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x ∧
          referenceCoreWallFloor K ≤ X 3 ∧
          HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve x 0 t))
            (normalizedEventRate projectiveActiveWall x 0 T) T ∧
          0 < normalizedEventRate projectiveActiveWall x 0 T ∧
          ContDiffAt ℝ 2 physicalEntranceData x := by
  obtain ⟨δ₀, hδ₀, C, hC, H⟩ := exists_compact_physicalEntrance_data (K := K) ha
  have hCpos : 0 < C := by linarith only [hC]
  let δ := min δ₀ (min (1 / (2 * C)) (referenceCoreWallFloor K / C))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₀ (lt_min (by positivity) (div_pos (referenceCoreWallFloor_pos K) hCpos))
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro k hk v hv x hc hx T X Y
  let z := fromProjectiveState (referenceEntranceState k v)
  let d := normalizedEuclideanDistance z x
  have hd : d ≤ δ := hx
  have hd₀ : d ≤ δ₀ := hd.trans (min_le_left _ _)
  have hdhalf : C * d ≤ 1 / 2 := by
    have H' : d ≤ (1 / 2) / C := by
      simpa only [div_div] using
        (show d ≤ 1 / (2 * C) from hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have HH := (le_div_iff₀ hCpos).mp H'
    nlinarith only [HH]
  have hdwall : C * d ≤ referenceCoreWallFloor K := by
    have H' := (le_div_iff₀ hCpos).mp (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H']
  obtain ⟨⟨hA, hvalid⟩, hreg, hval, herr⟩ := H k hk v hv x hd₀
  have Hact := physicalEntranceData_actual hc hA hvalid
  have hP : (physicalEntranceData x).2.1 = Y := Hact.2.1
  have hX : (physicalEntranceData x).2.2.1 = X := Hact.2.2.1
  have hv' : 0 < v ∧ v < 1 := ⟨ha.trans_le hv.1, by linarith only [hv.2]⟩
  rw [physicalEntranceData_reference hk.1 hv'] at herr
  let q := referencePulse k (-referenceHalfTime k)
  have hproj : ‖(physicalEntranceData x).2.1 - q‖ ≤ C * d :=
    (norm_fst_le _).trans ((norm_snd_le _).trans herr)
  have hphys : ‖(physicalEntranceData x).2.2.1 - fromProjectiveState q‖ ≤ C * d :=
    (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans herr))
  have hrad : |(physicalEntranceData x).2.2.2 - k| ≤ C * d :=
    (norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans herr))
  obtain ⟨hmq, hnq⟩ := referenceCore_endpoint_bounds hk
  have hM : |Y 0 - q 0| ≤ C * d := by
    rw [hP] at hproj
    exact (norm_le_pi_norm (Y - q) 0).trans hproj
  have hn : |X 3 - fromProjectiveState q 3| ≤ C * d := by
    rw [hX] at hphys
    exact (norm_le_pi_norm (X - fromProjectiveState q) 3).trans hphys
  have hT : T ≤ C := (le_abs_self T).trans ((norm_fst_le _).trans hval)
  have hM' : 1 < Y 0 := by
    change 2 ≤ q 0 at hmq
    have Hlo := (abs_le.mp hM).1
    linarith only [Hlo, hmq, hdhalf]
  have hn' : referenceCoreWallFloor K ≤ X 3 := by
    change 2 * referenceCoreWallFloor K ≤ fromProjectiveState q 3 at hnq
    have Hlo := (abs_le.mp hn).1
    linarith only [Hlo, hnq, hdwall]
  have hr' : |coreRadius (Y 0) (Y 2) - k| ≤ C * d := by
    change |coreRadius ((physicalEntranceData x).2.1 0) ((physicalEntranceData x).2.1 2) - k| ≤ _ at hrad
    rwa [hP] at hrad
  exact ⟨Hact.1, hT, hP ▸ Hact.2.2.2.1, hM', Hact.2.2.2.2.1, hr', hn',
    Hact.2.2.2.2.2.1, Hact.2.2.2.2.2.2, hreg⟩
