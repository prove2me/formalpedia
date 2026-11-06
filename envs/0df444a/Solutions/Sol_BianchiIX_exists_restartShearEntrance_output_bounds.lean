-- Prove2me | solution 1 for BianchiIX.exists_restartShearEntrance_output_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:51:00.828186+00:00
-- url     : https://prove2.me/submissions/f3f15c6b-969e-4296-94b3-9a107c2296bb

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_connectionReturn_restart_bounds
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_entrancePartialCore_reflection_values
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_restartShearEntrance_connection
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_core_budget {h M q P ε : ℝ} (hq : 3 < q) (hP : 4 < P) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) ≤ ε := by
  have Hq : ContinuousAt (fun r : ℝ => r ^ (q - 3)) 0 :=
    (Real.continuous_rpow_const (by linarith only [hq] : 0 ≤ q - 3)).continuousAt
  have HP : ContinuousAt (fun r : ℝ => r ^ (P - 4)) 0 :=
    (Real.continuous_rpow_const (by linarith only [hP] : 0 ≤ P - 4)).continuousAt
  have H : ContinuousAt (fun r : ℝ => 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4)) 0 :=
    (continuousAt_const.mul Hq).add (continuousAt_const.mul HP)
  have Hzero : 1024 * h * (0 : ℝ) ^ (q - 3) + 65536 * M * (0 : ℝ) ^ (P - 4) < ε := by
    simpa only [Real.zero_rpow (by linarith only [hq] : q - 3 ≠ 0),
      Real.zero_rpow (by linarith only [hP] : P - 4 ≠ 0), mul_zero, add_zero] using hε
  exact ((H.eventually (isOpen_Iio.mem_nhds Hzero)).filter_mono nhdsWithin_le_nhds).mono
    (fun _ hr => hr.le)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_core_amplitude_budget {r h M q P ζ k u p ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hk : 0 < k) (hkr : k ≤ 32 / r)
    (hu : 0 ≤ u ∧ u ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3) (hζ : ζ ≤ r ^ P)
    (hbudget : 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) ≤ ε) :
    u + p ≤ ε / k := by
  have Hsum : u + p ≤ 32 * h * r ^ (q - 2) + 2048 * M * r ^ P / r ^ 3 :=
    add_le_add hu.2 (hp.2.trans (by gcongr))
  have H := mul_le_mul hkr Hsum (add_nonneg hu.1 hp.1) (by positivity : 0 ≤ 32 / r)
  have Hq : r ^ (q - 3) = r ^ (q - 2) / r := by
    rw [show q - 3 = (q - 2) - 1 by ring, Real.rpow_sub hr, Real.rpow_one]
  have HP : r ^ (P - 4) = r ^ P / r ^ 4 := by
    simpa using Real.rpow_sub hr P (4 : ℕ)
  have Heq : 32 / r * (32 * h * r ^ (q - 2) + 2048 * M * r ^ P / r ^ 3) =
      1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) := by
    rw [Hq, HP]
    field_simp
    ring
  apply (le_div_iff₀ hk).mpr
  have H' : k * (u + p) ≤ ε := ((H.trans_eq Heq).trans hbudget)
  simpa only [mul_comm k] using H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_component_bounds (m v : ℝ) :
    |m - 1| ≤ coreRadius m v ∧ |v| ≤ coreRadius m v := by
  have hr : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg v]
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (m - 1)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_section_sign (m : ℝ) :
    (coreAngle m 1 < 0 ↔ 1 < m) ∧ (0 < coreAngle m 1 ↔ m < 1) := by
  simp only [coreAngle, div_one, Real.arsinh_neg_iff, Real.arsinh_pos_iff]
  constructor <;> constructor <;> intro h <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fromCoreAngleState_toCoreAngleState {y : ProjectiveState} (hv : 0 < y 2) :
    fromCoreAngleState (coreAngle (y 0) (y 2)) (toCoreAngleState y) = y := by
  ext i
  fin_cases i
  · exact (coreAngle_coordinates hv).2
  · rfl
  · exact (coreAngle_coordinates hv).1
  · change y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) = y 3
    rw [(coreAngle_coordinates hv).1]
    field_simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreAngle_entry_eq_neg_arcosh {m : ℝ} (hm : 1 < m) :
    coreAngle m 1 = -Real.arcosh (coreRadius m 1) := by
  have H := Real.arcosh_cosh (neg_nonneg.mpr ((coreAngle_section_sign m).1.mpr hm).le)
  rw [Real.cosh_neg, cosh_coreAngle (by norm_num : (0 : ℝ) < 1), div_one] at H
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_abs_le_arcosh {m v : ℝ} (hv : 1 ≤ v) :
    |coreAngle m v| ≤ Real.arcosh (coreRadius m v) := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hk0 := coreRadius_pos (m := m) hv0
  have Hcosh : Real.cosh (coreAngle m v) ≤ coreRadius m v := by
    rw [cosh_coreAngle hv0]
    exact div_le_self hk0.le hv
  have H := (Real.arcosh_le_arcosh (Real.cosh_pos _) hk0).mpr Hcosh
  rw [← Real.cosh_abs (coreAngle m v), Real.arcosh_cosh (abs_nonneg _)] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partialCoreEntry_region {y : ProjectiveState} {ε : ℝ}
    (hk : 6 ≤ coreRadius (y 0) (y 2)) (hv : 1 ≤ y 2)
    (hu : 0 ≤ y 1) (hp : 0 ≤ y 2 * y 3)
    (hε : ε ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ ε / coreRadius (y 0) (y 2)) :
    coreRegion (coreRadius (y 0) (y 2)) y := by
  have hk0 : 0 < coreRadius (y 0) (y 2) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have Hcap := hsmall.trans (div_le_div_of_nonneg_right hε hk0.le)
  refine ⟨?_, hv, ⟨hu, ?_⟩, ⟨hp, ?_⟩⟩
  · rw [coreRadius_sq, sub_self, abs_zero]
    norm_num
  · linarith only [Hcap, hp]
  · linarith only [Hcap, hu]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_walls_nonincreasing {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ y 1 ∧ entranceReturnState y 3 ≤ y 3 := by
  have H := entranceReturn_decay hk hm hu hv hw
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hEs : Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) hL) (by norm_num))
  have hEw : Real.exp (-(-Real.log (y 2)) / coreRadius (y 0) (y 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  constructor
  · exact H.1.trans ((mul_le_mul_of_nonneg_left hEs (mul_nonneg hu.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hu.1]))
  · exact H.2.trans ((mul_le_mul_of_nonneg_left hEw (mul_nonneg hw.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hw.1]))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_partialCore_entry {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let k := coreRadius (y 0) (y 2)
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    6 ≤ κ ∧ (99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k) ∧
      z 2 = 1 ∧ 1 < z 0 ∧ coreRegion κ z ∧
      (0 ≤ z 1 ∧ z 1 ≤ y 1) ∧ (0 ≤ z 3 ∧ z 3 ≤ y 2 * y 3) ∧
      z 1 + z 2 * z 3 ≤ η / κ ∧ projectiveCoreAngle z = -Real.arcosh κ := by
  intro k z κ
  have hk' : 7 / 4 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have HE := (entranceReturn_regular hk' hm hu hv hw).1
  have HR := entranceReturn_region hk' hm hu hv hw _ ⟨HE.1.1.1.le, le_rfl⟩
  change entranceRegion k z at HR
  have hκ : 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k := by
    have H := abs_le.mp HR.2.1
    change - (k / 100) ≤ κ - k ∧ κ - k ≤ k / 100 at H
    constructor <;> linarith only [H.1, H.2]
  have hκ6 : 6 ≤ κ := by linarith only [hk, hκ.1]
  have hκ0 : 0 < κ := by linarith only [hκ6]
  have hhit : z 2 = 1 := (entranceReturn_active_component hk' hm hu hv hw).1
  have hm' : 1 < z 0 := by
    have H := (entranceRegion_phase hk' HR).1
    linarith only [H, hk]
  have hU := (entranceReturn_walls_nonincreasing hk' hm hu hv hw).1
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hExp : Real.exp (-(-Real.log (y 2)) / k) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  have hW : z 3 ≤ y 2 * y 3 := (entranceReturn_decay hk' hm hu hv hw).2.trans
    ((mul_le_of_le_one_right (mul_nonneg hw.1 hv.1.le) hExp).trans_eq (mul_comm _ _))
  have hsum : z 1 + z 2 * z 3 ≤ η / κ := by
    rw [hhit, one_mul]
    exact (add_le_add hU hW).trans (hsmall.trans
      (div_le_div_of_nonneg_left hη.1.le hκ0 (by linarith only [hκ.2, hk0])))
  have hprod : 0 ≤ z 2 * z 3 := mul_nonneg HR.2.2.2.1.1 HR.2.2.2.2.1
  refine ⟨hκ6, hκ, hhit, hm', partialCoreEntry_region hκ6 (by rw [hhit])
    HR.2.2.1.1 hprod hη.2 hsum, ⟨HR.2.2.1.1, hU⟩, ⟨HR.2.2.2.2.1, hW⟩, hsum, ?_⟩
  change coreAngle (z 0) (z 2) = -Real.arcosh (coreRadius (z 0) (z 2))
  rw [hhit]
  exact coreAngle_entry_eq_neg_arcosh hm'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionDefect {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t) :
    HasDerivAt (fun x => restartProjectionDefect (p x))
      (restartProjectionDefectTangent (p t) v) t := by
  have Hn : HasDerivAt (fun x => (p x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hc (i : Fin 3) : HasDerivAt (fun x => (p x).2 i) (v.2 i) t := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact P.hasFDerivAt.comp_hasDerivAt t
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H)
  have HD := ((Hc 0).pow 2).add
    ((((Hn.pow 2).add ((Hc 1).pow 2)).add ((Hc 2).pow 2)).const_mul 2)
  have HD' := HD.sub (((Hn.add (Hc 1)).add (Hc 2)).pow 2)
  convert! HD' using 1
  · funext x
    dsimp [restartProjectionDefect, curvature]
    ring
  · dsimp [restartProjectionDefectTangent]
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefectTangent_bound {p v : RestartRadialState} {R D : ℝ}
    (hp : ‖p‖ ≤ R) (hv : ‖v‖ ≤ D) :
    |restartProjectionDefectTangent p v| ≤ 32 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  have vn : |v.1| ≤ D := (norm_fst_le v).trans hv
  have vc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ps : |p.1 + p.2 1 + p.2 2| ≤ 3 * R :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [pn, pc 1, pc 2])
  have vs : |v.1 + v.2 1 + v.2 2| ≤ 3 * D :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [vn, vc 1, vc 2])
  have Hsum : |p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2| ≤ 3 * R * D := by
    calc
      _ ≤ |p.1 * v.1| + |p.2 1 * v.2 1| + |p.2 2 * v.2 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R * D + R * D + R * D := by
        simp only [abs_mul]
        gcongr
        · exact pc 1
        · exact vc 1
        · exact pc 2
        · exact vc 2
      _ = _ := by ring
  unfold restartProjectionDefectTangent
  calc
    _ ≤ |2 * p.2 0 * v.2 0| + |4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
        |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
      have HT : |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
          2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| ≤
          |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
          |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
        simpa using (abs_sub_le (2 * p.2 0 * v.2 0 + 4 *
          (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)) 0
          (2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)))
      exact HT.trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * R * D + 4 * (3 * R * D) + 2 * (3 * R) * (3 * D) := by
      norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      · exact pc 0
      · exact vc 0
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_eq_sqrt {p : RestartRadialState}
    (hd : restartProjectionDefect p ≤ 1) :
    restartProjectionHeight p = 1 - Real.sqrt (1 - restartProjectionDefect p) := by
  have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect p)
  apply (div_eq_iff (by positivity : 1 + Real.sqrt (1 - restartProjectionDefect p) ≠ 0)).mpr
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionHeight {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) < 1) :
    HasDerivAt (fun x => restartProjectionHeight (p x))
      (restartProjectionDefectTangent (p t) v / (2 * Real.sqrt (1 - restartProjectionDefect (p t)))) t := by
  have HD := hasDerivAt_restartProjectionDefect H
  have HS := ((HD.const_sub 1).sqrt (by linarith only [hd] : 1 - restartProjectionDefect (p t) ≠ 0)).const_sub 1
  have Heq : (fun x => restartProjectionHeight (p x)) =ᶠ[𝓝 t]
      fun x => 1 - Real.sqrt (1 - restartProjectionDefect (p x)) := by
    filter_upwards [HD.continuousAt.eventually (isOpen_Iio.mem_nhds hd)] with x hx
    exact restartProjectionHeight_eq_sqrt hx.le
  convert! HS.congr_of_eventuallyEq Heq using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_derivative_bound {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t R D : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) ≤ 1 / 2) (hp : ‖p t‖ ≤ R) (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (fun x => restartProjectionHeight (p x)) t ∧
      |deriv (fun x => restartProjectionHeight (p x)) t| ≤ 32 * R * D := by
  have HD := hasDerivAt_restartProjectionHeight H (by linarith only [hd])
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - restartProjectionDefect (p t)))]
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - restartProjectionDefect (p t)) := by
    have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect (p t))
    nlinarith only [Hsq, Real.sqrt_nonneg (1 - restartProjectionDefect (p t)), hd]
  exact (div_le_self (abs_nonneg _) (by linarith only [hsqrt])).trans
    (restartProjectionDefectTangent_bound hp hv)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    a ^ 2 / 2 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 6 * a ^ 2 := by
  have hsig : σ ^ 2 = 1 := by nlinarith only [sq_abs σ, hσ]
  have hsq : (σ * p.2 0) ^ 2 = (p.2 0) ^ 2 := by rw [mul_pow, hsig, one_mul]
  have hslo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ 3 * a / 4) hs.1 2
  have hshi := pow_le_pow_left₀ (by linarith only [hs.1, ha.1] : 0 ≤ σ * p.2 0) hs.2 2
  rw [hsq] at hslo hshi
  have hsum : p.2 1 + p.2 2 ≤ a / 8 := by linarith only [h₂.2, h₃.2]
  have hcross := mul_le_mul hn.2 hsum (add_nonneg h₂.1 h₃.1) (sq_nonneg a)
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha3 : a ^ 2 * a ≤ a ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
  have hnsq := pow_le_pow_left₀ hn.1 hn.2 2
  have hdiff : |p.2 1 - p.2 2| ≤ a / 16 :=
    abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩
  have hdsq := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hdsq
  have heq : restartProjectionDefect p = (p.2 0) ^ 2 + p.1 ^ 2 + (p.2 1 - p.2 2) ^ 2 -
      2 * p.1 * (p.2 1 + p.2 2) := by unfold restartProjectionDefect curvature; ring
  constructor
  · rw [heq]
    have ha3small := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)
    nlinarith only [hslo, hcross, ha3small, sq_nonneg p.1, sq_nonneg (p.2 1 - p.2 2), sq_nonneg a]
  · rw [heq]
    have hneg := mul_nonneg hn.1 (add_nonneg h₂.1 h₃.1)
    have hnsmall := mul_le_mul_of_nonneg_left ha.2 ha.1.le
    have hn4small := mul_le_mul_of_nonneg_left hnsmall (sq_nonneg a)
    nlinarith only [hshi, hnsq, hn4small, hdsq, hneg, ha3, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    restartProjectionDefect p ≤ 1 / 2 ∧
      a ^ 2 / 4 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 6 * a ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_shear_bounds ha hσ hs hn h₂ h₃
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by nlinarith only [Hhi, ha.1, ha.2]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨hd1, (le_div_iff₀ hden).mpr ?_, (div_le_iff₀ hden).mpr ?_⟩
  · nlinarith only [Hlo, mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg a)]
  · nlinarith only [Hhi, mul_nonneg (sq_nonneg a) hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearCurve_annulus {a ρ σ ε n₂ n₃ : ℝ} (ha : 0 < a)
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    ‖restartShearCurve σ n₂ n₃ ρ‖ ≤ 2 * a ∧
      a ≤ restartRadialNorm (restartShearCurve σ n₂ n₃ ρ) ∧ |n₂ - n₃| ≤ 2 * ε * a := by
  have hρpos := ha.trans_le hρ.1
  have hsmall : 2 * ε * a ≤ 2 * a := by nlinarith only [hε.2, ha]
  refine ⟨?_, ?_, abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |σ * ρ| ≤ 2 * a
      simpa only [abs_mul, hσ, abs_of_pos hρpos, one_mul] using hρ.2
    · exact (show |n₂| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₂.1] using h₂.2).trans hsmall
    · exact (show |n₃| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₃.1] using h₃.2).trans hsmall
  · have H := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (n₂ - n₃)) :
        (σ * ρ) ^ 2 ≤ (σ * ρ) ^ 2 + (n₂ - n₃) ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_mul, hσ, abs_of_pos hρpos, one_mul] at H
    exact hρ.1.trans H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastShearProjectiveEntry_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T σ n₂ n₃) ρ ∧
          DifferentiableAt ℝ (restartFastShearHeight h T σ n₂ n₃) ρ ∧
          a ^ 2 / 4 ≤ restartFastShearHeight h T σ n₂ n₃ ρ ∧
          restartFastShearHeight h T σ n₂ n₃ ρ ≤ 6 * a ^ 2 ∧
          |deriv (restartFastShearHeight h T σ n₂ n₃) ρ| ≤ 512 * a ∧
          (1 / (8 * a) ≤ σ * y 0 ∧ σ * y 0 ≤ 18 / a) ∧
          (0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2)) ∧
          (n₂ / (12 * a ^ 2) ≤ y 2 ∧ y 2 ≤ 16 * n₂ / a ^ 2) ∧
          (n₃ / (12 * a ^ 2) ≤ y 3 ∧ y 3 ≤ 16 * n₃ / a ^ 2) ∧
          (0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 64 * ε / a) ∧
          (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4) := by
  obtain ⟨C, _, h₀, hh₀, H₀⟩ := exists_restartShearFastEntry_control
  refine ⟨min h₀ 1, lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨astar, hastar, Ha⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T y
  let Z := restartShearCurve σ n₂ n₃ ρ
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let p := restartSectionRadialState h T Z
  obtain ⟨ha1, hasmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hshear, hc, hv, _, hw⟩ :=
    Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change 0 < x 2 at hnpos
  change x 2 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * x 1 ∧ σ * x 1 ≤ 9 * a / 4 at hshear
  have hnsq : p.1 ≤ a ^ 2 := hnexp.trans (by
    have HP : a ^ q ≤ a ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq.le
    exact (mul_le_mul_of_nonneg_left HP hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans (min_le_right _ _))))
  have Hweak (i : Fin 2) : 0 ≤ p.2 i.succ ∧ p.2 i.succ ≤ a / 16 := by
    have hZi : 0 ≤ Z i.succ ∧ Z i.succ ≤ 2 * ε * a := by fin_cases i; exact h₂; exact h₃
    constructor
    · exact (div_nonneg hZi.1 (by norm_num)).trans (hw i).1
    · have H := (hw i).2.1.trans (mul_le_mul_of_nonneg_left hZi.2 (by norm_num))
      nlinarith only [H, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have hpsmall : ‖p‖ ≤ 8 * a := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos (show 0 < p.1 from hnpos)]
    refine ⟨hnsq.trans ?_, hc⟩
    nlinarith only [ha.1, ha1]
  obtain ⟨hd, Hlo, Hhi⟩ := restartProjectionHeight_shear_bounds
    ⟨ha.1, by linarith only [hasmall]⟩ hσ hshear ⟨hnpos.le, hnsq⟩ (Hweak 0) (Hweak 1)
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT (by linarith only [hneg])).comp_tendsto
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  change (fun t => restartProjectionHeight (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) =ᶠ[𝓝 ρ]
    restartFastShearHeight h T σ n₂ n₃ at Hgerm
  have HD := restartProjectionHeight_derivative_bound Hcurve hd hpsmall hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  change a ^ 2 / 4 ≤ restartProjectionHeight p at Hlo
  change restartProjectionHeight p ≤ 6 * a ^ 2 at Hhi
  have heq : restartProjectionHeight p = 1 + x 0 := Hgerm.eq_of_nhds
  rw [heq] at Hlo Hhi
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le Hlo
  have Hchart := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).comp ρ
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).differentiableAt
  have HX := (hasFDerivAt_normalizedMaxCurve_initial hdom).differentiableAt.comp ρ Hchart
  have HY := ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HX
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have Hcoord (u u₀ : ℝ) (hu₀ : 0 ≤ u₀) (hu : u₀ / 2 ≤ u ∧ u ≤ 2 * u₀) :
      u₀ / (12 * a ^ 2) ≤ Real.sqrt 3 * u / (1 + x 0) ∧
        Real.sqrt 3 * u / (1 + x 0) ≤ 16 * u₀ / a ^ 2 := by
    have hu0 : 0 ≤ u := (div_nonneg hu₀ (by norm_num)).trans hu.1
    constructor
    · calc
        _ = (u₀ / 2) / (6 * a ^ 2) := by ring
        _ ≤ _ := div_le_div₀ (by positivity)
          (hu.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hu0])) hA Hhi
    · calc
        _ ≤ (4 * u₀) / (a ^ 2 / 4) := div_le_div₀ (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hu0, hu.2]) (by positivity [ha.1]) Hlo
        _ = _ := by ring
  have HV := Hcoord (x 3) n₂ h₂.1 ⟨(hw 0).1, (hw 0).2.1⟩
  have HW := Hcoord (x 4) n₃ h₃.1 ⟨(hw 1).1, (hw 1).2.1⟩
  have hyV : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hyW : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  refine ⟨hdom, HY, Hactual.differentiableAt, Hlo, Hhi, ?_, ?_, ?_, HV, HW, ?_, ?_⟩
  · rw [Hactual.deriv]
    exact HD.2.trans (by ring_nf; rfl)
  · have heqM : σ * y 0 = Real.sqrt 3 * (σ * x 1) / (1 + x 0) := by
      change σ * (Real.sqrt 3 * x 1 / (1 + x 0)) = _
      ring
    rw [heqM]
    have hspos : 0 ≤ σ * x 1 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hshear.1
    constructor
    · calc
        _ = (3 * a / 4) / (6 * a ^ 2) := by field_simp; ring
        _ ≤ _ := div_le_div₀ (by positivity [ha.1])
          (hshear.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hspos])) hA Hhi
    · calc
        _ ≤ (2 * (9 * a / 4)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [ha.1])
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hspos, hshear.2]) (by positivity [ha.1]) Hlo
        _ = _ := by field_simp; ring
  · refine ⟨div_pos (mul_pos hsqrt hnpos) hA, ?_⟩
    calc
      y 1 ≤ (2 * (h * a ^ q)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [hh.1, ha.1])
        (by
          change Real.sqrt 3 * x 2 ≤ 2 * (h * a ^ q)
          nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hnpos.le, hnexp]) (by positivity [ha.1]) Hlo
      _ = _ := by rw [Real.rpow_sub ha.1, Real.rpow_two]; ring
  · refine ⟨add_nonneg hyV hyW, ?_⟩
    calc
      y 2 + y 3 ≤ 16 * n₂ / a ^ 2 + 16 * n₃ / a ^ 2 := add_le_add HV.2 HW.2
      _ ≤ 16 * (2 * ε * a) / a ^ 2 + 16 * (2 * ε * a) / a ^ 2 := by gcongr; exact h₂.2; exact h₃.2
      _ = _ := by field_simp; ring
  · refine ⟨mul_nonneg hyV hyW, ?_⟩
    calc
      y 2 * y 3 ≤ (16 * n₂ / a ^ 2) * (16 * n₃ / a ^ 2) :=
        mul_le_mul HV.2 HW.2 hyW (by positivity [h₂.1])
      _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearCore_geometry {a m v : ℝ} (ha : a ∈ Ioc (0 : ℝ) (1 / 128))
    (hm : 1 / (8 * a) ≤ m ∧ m ≤ 18 / a) (hv : 0 ≤ v ∧ v ≤ 1 / a) :
    1 < m ∧ 6 ≤ coreRadius m v ∧ 1 / (16 * a) ≤ coreRadius m v ∧
      coreRadius m v ≤ 32 / a ∧
      (1 ≤ v → coreAngle m v ∈ Icc (-Real.arcosh (coreRadius m v)) 0) := by
  have hapos := ha.1
  have hm1 : 1 < m := lt_of_lt_of_le
    ((lt_div_iff₀ (by positivity : 0 < 8 * a)).mpr (by linarith only [ha.2])) hm.1
  have hgap : 1 / (16 * a) ≤ m - 1 := by
    have H : (1 : ℝ) ≤ 1 / (16 * a) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [ha.2])
    have heq : 1 / (8 * a) = 2 * (1 / (16 * a)) := by ring
    rw [heq] at hm
    linarith only [hm.1, H]
  have hklo := hgap.trans ((le_abs_self _).trans (coreRadius_component_bounds m v).1)
  have hk6 : 6 ≤ coreRadius m v := le_trans
    ((le_div_iff₀ (by positivity : 0 < 16 * a)).mpr (by linarith only [ha.2])) hklo
  have hkadd : coreRadius m v ≤ m + v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith only [hm1, hv.1])).mp
    change coreRadius m v ^ 2 ≤ (m + v) ^ 2
    rw [coreRadius_sq]
    unfold coreEnergy
    nlinarith only [hm1, mul_nonneg (by linarith only [hm1] : 0 ≤ m) hv.1]
  have hkhi : coreRadius m v ≤ 32 / a := hkadd.trans (by
    have H := add_le_add hm.2 hv.2
    have H19 : (18 : ℝ) / a + 1 / a ≤ 32 / a := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) ha.1.le
    exact H.trans H19)
  refine ⟨hm1, hk6, hklo, hkhi, ?_⟩
  intro hv1
  refine ⟨(abs_le.mp (coreAngle_abs_le_arcosh hv1)).1, ?_⟩
  change Real.arsinh ((1 - m) / v) ≤ 0
  have H : (1 - m) / v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [hm1]) hv.1
  simpa only [Real.arsinh_zero] using Real.arsinh_le_arsinh.mpr H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastShearCore_geometry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
        (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ
          let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
          let z := restartFastShearCoreAngle h T 1 n₂ n₃ ρ
          0 ≤ T ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
          0 < restartFastShearHeight h T 1 n₂ n₃ ρ ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T 1 n₂ n₃) ρ ∧
          1 < y 0 ∧ 6 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧
          (1 ≤ y 2 → z ∈ Icc (-Real.arcosh k) 0) := by
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hP (1 / 16), lt_min hhP (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨aP, haP, HaP⟩ := HP h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨min aP (1 / 128), lt_min haP (by norm_num), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ ρ hρ T y k z
  have ha128 : a ≤ 1 / 128 := ha.2.trans (min_le_right _ _)
  obtain ⟨Hdom, HY, _, HA, _, _, HM, _, HV, HW, HS, _⟩ :=
    HaP a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 1 / (8 * a) ≤ 1 * y 0 ∧ 1 * y 0 ≤ 18 / a at HM
  simp only [one_mul] at HM
  have hv0 : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hw0 : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  have hvhi : y 2 ≤ 1 / a := by
    have H : y 2 + y 3 ≤ 64 * ε / a := HS.2
    have HB : 64 * ε / a ≤ 1 / a := div_le_div_of_nonneg_right
      (by linarith only [hε.2]) ha.1.le
    linarith only [H, HB, hw0]
  have HG := shearCore_geometry ⟨ha.1, ha128⟩ HM ⟨hv0, hvhi⟩
  have hsmall : ‖restartShearCurve 1 n₂ n₃ ρ‖ ≤ 1 / 16 :=
    (restartShearCurve_annulus ha.1 hρ (by norm_num) hε h₂ h₃).1.trans
      (by linarith only [ha128])
  have hrad := restartSectionRadicand_pos_of_small
    (by rw [abs_of_pos hh.1]; exact hh.2.trans (min_le_right _ _)) hsmall
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq])
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [ha128])))
  exact ⟨hT, hrad, Hdom, (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le HA, HY, HG⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearPartialCore_entry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let y := restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ
            let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
            let z := restartFastShearCoreAngle h T 1 n₂ n₃ ρ
            0 ≤ T ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            0 < restartFastShearHeight h T 1 n₂ n₃ ρ ∧
            1 < y 0 ∧ 6 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧
            toCoreAngleState y 0 = k ∧ 0 < y 1 ∧ 0 ≤ y 2 * y 3 ∧
            y 1 + y 2 * y 3 ≤ η / k ∧
            (1 ≤ y 2 → z ∈ Icc (-Real.arcosh k) 0 ∧
              fromCoreAngleState z (toCoreAngleState y) = y ∧ coreRegion k y ∧
              (1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0))) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartFastShearCore_geometry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hG hV, lt_min hhG hhV, ?_⟩
  intro h hh q P hq hP η hη
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq2
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq2
  obtain ⟨aB, haB, HaB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_budget (h := h) (M := 1) hq hP hη.1)
  refine ⟨min aG (min aV aB), lt_min haG (lt_min haV haB), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ T y k z
  have hapos := ha.1
  obtain ⟨hT, hrad, hdom, hA, _, hm, hk, hklo, hkhi, hz⟩ :=
    HaG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, hu, _, _, _, hp⟩ :=
    HaV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 6 ≤ k at hk
  change k ≤ 32 / a at hkhi
  change 0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2) at hu
  change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4 at hp
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have hn₂ : n₂ ≤ a := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    nlinarith only [h₂.2, H, ha.1]
  have HU : 0 ≤ y 1 ∧ y 1 ≤ 32 * h * a ^ (q - 2) := ⟨hu.1.le, hu.2.trans (by
    nlinarith only [mul_nonneg hh.1.le (Real.rpow_nonneg ha.1.le (q - 2))])⟩
  have HP : 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * 1 * n₃ / a ^ 3 := by
    refine ⟨hp.1, hp.2.trans ?_⟩
    calc
      _ ≤ 256 * a * n₃ / a ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hn₂]) h₃.1) (by positivity)
      _ = 256 * n₃ / a ^ 3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) h₃.1) (by positivity)
  have HB := HaB ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hbudget : y 1 + y 2 * y 3 ≤ η / k :=
    restart_core_amplitude_budget ha.1 (by norm_num : (0 : ℝ) ≤ 1) hk0 hkhi HU HP h₃P HB
  refine ⟨hT, hrad, hdom, hA, hm, hk, hklo, hkhi, rfl, hu.1, hp.1, Hbudget, ?_⟩
  intro hv
  refine ⟨hz hv, fromCoreAngleState_toCoreAngleState (zero_lt_one.trans_le hv),
    partialCoreEntry_region hk hv hu.1.le hp.1 hη.2 Hbudget, ?_⟩
  rcases eq_or_lt_of_le hv with heq | hlt
  · exact Or.inr ⟨heq.symm, hm.le⟩
  · exact Or.inl hlt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearEntrance_inputs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
              y 2 < 1 →
              0 ≤ s ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
              s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
              0 < restartFastShearHeight h s 1 n₂ n₃ ρ ∧
              8 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧ 1 < y 0 ∧
              (0 < y 1 ∧ y 1 ≤ 1 / 10000) ∧ (0 < y 2 ∧ y 2 < 1) ∧
              (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) ∧ y 1 + y 2 * y 3 ≤ η / (2 * k) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hE hV, lt_min hhE hhV, ?_⟩
  intro h hh q P hq hP η hη
  have hηhalf : η / 2 ∈ Ioc (0 : ℝ) (1 / 10000) := ⟨by positivity [hη.1], by linarith only [hη.2]⟩
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP (η / 2) hηhalf
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aE (min aV (1 / 512)), lt_min haE (lt_min haV (by norm_num)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y k hv
  have haV' := ha.2.trans (min_le_right _ _)
  have ha512 : a ≤ 1 / 512 := haV'.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := ha512.trans (by norm_num)
  obtain ⟨hs, hrad, hdom, hA, hm, _, hklo, hkhi, _, hu0, hp0, hsum, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, hV, hW, _⟩ :=
    HaV a ⟨ha.1, haV'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) ⟨h₂.1.le, h₂.2⟩ h₃ ρ hρ
  have hk8 : 8 ≤ k := (show 8 ≤ 1 / (16 * a) by
    apply (le_div_iff₀ (by positivity [ha.1])).mpr
    linarith only [ha512]).trans hklo
  have hsmall : y 1 + y 2 * y 3 ≤ η / (2 * k) := hsum.trans_eq (by ring)
  have hu : y 1 ≤ 1 / 10000 := ((le_add_of_nonneg_right hp0).trans hsmall).trans
    ((div_le_self hη.1.le (by linarith only [hk8])).trans hη.2)
  have hv0 : 0 < y 2 := (div_pos h₂.1 (by positivity [ha.1])).trans_le hV.1
  have hw0 : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans hW.1
  have hn₃ : n₃ ≤ a ^ (4 : ℕ) := h₃P.trans (by
    have H := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hP.le
    rw [show a ^ (4 : ℝ) = a ^ (4 : ℕ) from Real.rpow_natCast a 4] at H
    exact H)
  have hw : y 3 ≤ 1 / 10000 := by
    calc
      _ ≤ 16 * n₃ / a ^ 2 := hW.2
      _ ≤ 16 * a ^ 4 / a ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn₃ (by norm_num)) (sq_nonneg a)
      _ = 16 * a ^ 2 := by field_simp
      _ ≤ _ := by
        have H := pow_le_pow_left₀ ha.1.le ha512 2
        norm_num at H
        linarith only [H]
  exact ⟨hs, hrad, hdom, hA, hk8, hklo, hkhi, hm, ⟨hu0, hu⟩, ⟨hv0, hv⟩, ⟨hw0, hw⟩, hsmall⟩

end
end

/-- Below V = 1, the complete reflected return retains the initial two-wall product budget. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let p := restartShearReturnParameters h s n₂ n₃ ρ
            let G := restartShearReturnState h s n₂ n₃ ρ
            y 2 < 1 → connectionReturnValid p ∧ s < restartShearReturnTime h s n₂ n₃ ρ ∧
              1 / (64 * a) ≤ G 0 ∧ G 0 ≤ 64 / a ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve x 0 (restartShearReturnTime h s n₂ n₃ ρ))) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearEntrance_inputs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearEntrance_connection
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hI (min hC hV), lt_min hhI (lt_min hhC hhV), ?_⟩
  intro h hh q P hq hP
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aI (min aC aV), lt_min haI (lt_min haC haV), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y x p G hv
  have ha' := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, hk, hklo, hkhi, hm, hu, hv', hw, hsmall⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨hT, _, _, hμ, hU, hW, _, hweak, _, hvalid, horbit, _⟩ :=
    HaC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, _, _, _, _, hWfast, _, hprod⟩ :=
    HaV a ⟨ha.1, ha'.trans (min_le_right _ _)⟩ ε 1 n₂ n₃ hε (by norm_num)
      ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  have hwpos : 0 < y 3 := (div_pos h₃.1 (by positivity [ha.1])).trans_le hWfast.1
  let z := entranceReturnState y
  let κ := coreRadius (z 0) (z 2)
  let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
  obtain ⟨_, hκrange, _, _, _, _, hWe, _, _⟩ :=
    entranceReturn_partialCore_entry hk hm.le ⟨hu.1.le, hu.2⟩ hv' hw
      ⟨by norm_num, le_rfl⟩ hsmall
  change 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k at hκrange
  change 1 / (16 * a) ≤ k at hklo
  change k ≤ 32 / a at hkhi
  have Hvalues := entrancePartialCore_reflection_values hk hm.le hu hv' ⟨hwpos, hw.2⟩
    ⟨by norm_num, le_rfl⟩ hsmall
  change κ / 2 ≤ p 0 ∧ (1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3) ∧ κ / 2 ≤ G 0 ∧ G 0 ≤ κ ∧ _ at Hvalues
  obtain ⟨_, _, Hstrong, Hweak, Hsum, Hentry⟩ := connectionReturn_restart_bounds hμ.1 hU hW
  have hκlo : 1 / (32 * a) ≤ κ := by
    have Heq : 1 / (16 * a) = 2 * (1 / (32 * a)) := by ring
    rw [Heq] at hklo
    have H : 0 ≤ 1 / (32 * a) := by positivity [ha.1]
    linarith only [hklo, hκrange.1, H]
  have hκhi : κ ≤ 64 / a := calc
    _ ≤ 101 / 100 * k := hκrange.2
    _ ≤ 101 / 100 * (32 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
    _ = (808 / 25) / a := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) ha.1.le
  refine ⟨hvalid, ?_, ?_, Hvalues.2.2.2.1.trans hκhi, Hstrong.1, Hweak.1, ?_, ?_⟩
  · have htc : 0 < connectionReturnTime p := hvalid.1.1.1
    change s < s + partialCoreDownwardReturnTime y + connectionReturnTime p
    linarith only [hT, htc]
  · calc
      _ = (1 / (32 * a)) / 2 := by ring
      _ ≤ κ / 2 := div_le_div_of_nonneg_right hκlo (by norm_num)
      _ ≤ _ := Hvalues.2.2.1
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left
      (hweak.trans (hWe.2.trans hprod.2)) (by norm_num)).trans_eq (by ring))
  · rw [horbit] at Hentry
    exact Hentry
