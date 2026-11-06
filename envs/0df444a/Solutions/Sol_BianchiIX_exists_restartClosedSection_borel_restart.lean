-- Prove2me | solution 1 for BianchiIX.exists_restartClosedSection_borel_restart
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:18:02.760754+00:00
-- url     : https://prove2.me/submissions/00332160-7624-405c-afbd-0fec05262915

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_measurable_radial_restart
import Theorems.Thm_BianchiIX_exists_restartConnection_output_bounds
import Theorems.Thm_BianchiIX_exists_restartConnection_output_phase
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartRadialCurve_control
import Theorems.Thm_BianchiIX_exists_restartRadialFailure_quantitative
import Theorems.Thm_BianchiIX_exists_restartReturn_joint_regular
import Theorems.Thm_BianchiIX_exists_restartShearReturn_common_bounds
import Theorems.Thm_BianchiIX_exists_restartShearReturn_common_regular
import Theorems.Thm_BianchiIX_mainWallOriginalMeasure_closedFailure
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < dyadicScale d j := by
  exact mul_pos hd (pow_pos (by norm_num) _)

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_le {d : ℝ} (hd : 0 ≤ d) (j : ℕ) : dyadicScale d j ≤ d :=
  mul_le_of_le_one_right hd (pow_le_one₀ (by norm_num) (by norm_num))

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
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_constraint {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : stateConstraint (mainWallChart h y) = 1 := by
  have H := Real.sq_sqrt hy.le
  dsimp [stateConstraint, constraint, shearSq, mainWallChart]
  rw [neg_sq, H]
  unfold mainWallRadicand
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toProjectiveState_axisSwap (x : NormalizedState) :
    toProjectiveState (axisSwap x) = projectiveReflection (toProjectiveState x) := by
  ext i
  fin_cases i <;> dsimp [toProjectiveState, axisSwap, projectiveReflection, projectiveCoord]
  all_goals ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallRadicand_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallRadicand h (mainWallReflection y) = mainWallRadicand h y := by
  dsimp [mainWallRadicand, mainWallReflection, curvature]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallChart h (mainWallReflection y) = axisSwap (mainWallChart h y) := by
  simp only [mainWallChart, mainWallRadicand_reflection]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedMaxDomain_mainWallReflection (h t₀ : ℝ) (y : SectionCoordinates) :
    normalizedMaxDomain (mainWallChart h (mainWallReflection y)) t₀ =
      normalizedMaxDomain (mainWallChart h y) t₀ := by
  rw [mainWallChart_reflection]
  exact NormalizedSymmetry.swap.maxDomain _ _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedMaxCurve_mainWallReflection {h t₀ t : ℝ} {y : SectionCoordinates}
    (ht : t ∈ normalizedMaxDomain (mainWallChart h y) t₀) :
    normalizedMaxCurve (mainWallChart h (mainWallReflection y)) t₀ t =
      axisSwap (normalizedMaxCurve (mainWallChart h y) t₀ t) := by
  rw [mainWallChart_reflection]
  exact NormalizedSymmetry.swap.maxCurve ht

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
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_mainWallChartDensity (h : ℝ) : Measurable (mainWallChartDensity h) := by
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    mainWallChart mainWallRadicand curvature wallAmplitude
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalDensity_eq {h : ℝ} (hh : 0 < h) (z : SectionCoordinates) :
    mainWallOriginalDensity h z =
      (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2))) * mainWallChartDensity h z := by
  have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  unfold mainWallOriginalDensity mainWallChartDensity correctedSectionFluxDensity
  exact (mul_div_cancel₀ _ (by positivity : 1 + 4 * wallAmplitude h (Real.exp (-z 1))
    (Real.exp (-z 2)) ≠ 0)).symm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_eq_withDensity {h : ℝ} (hh : 0 < h) :
    mainWallOriginalMeasure h = (mainWallMeasure h).withDensity
      (fun z => ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
  have hw : Measurable (fun z : SectionCoordinates =>
      ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
    unfold wallAmplitude
    fun_prop
  unfold mainWallOriginalMeasure mainWallMeasure
  rw [← withDensity_mul _ (measurable_mainWallChartDensity h).ennreal_ofReal hw]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  dsimp only [Pi.mul_apply]
  rw [mainWallOriginalDensity_eq hh, ENNReal.ofReal_mul (by positivity)]
  exact mul_comm _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_le_original {h : ℝ} (hh : 0 < h) :
    mainWallMeasure h ≤ mainWallOriginalMeasure h := by
  rw [mainWallOriginalMeasure_eq_withDensity hh]
  have H : (fun _ : SectionCoordinates => (1 : ℝ≥0∞)) ≤ᵐ[mainWallMeasure h]
      (fun z => ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
    apply Filter.Eventually.of_forall
    intro z
    have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
      Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  simpa using withDensity_mono H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialPieceInverse_map {d ε : ℝ} (hd : 0 < d) {i : RadialPieceIndex}
    {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i) :
    radialPieceInverse i.1 (radialPieceMap i.1 z) = z := by
  rcases i with ⟨neg | other, j⟩
  · have h₁ : 0 < z 1 := hz.1
    have h₂ : 0 < z 2 := hz.2.1
    cases neg <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, signedShearLogCoordinates, Real.exp_log h₁, Real.exp_log h₂]
  · have hr : 0 < z 0 := (dyadicScale_pos hd j).trans hz.2.2.1.1
    have hζ : 0 < z 2 := hz.2.1
    cases other <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, mainWallReflection, Real.exp_log hr, Real.exp_log hζ, hr.ne']

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_mainWallOpenSection (d : ℝ) : MeasurableSet (mainWallOpenSection d) := by
  have hs : MeasurableSet {z : SectionCoordinates | |z 0| < d} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hm : MeasurableSet {z : SectionCoordinates | max (Real.exp (-z 1)) (Real.exp (-z 2)) < d} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact hs.inter hm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.signedShearLogCoordinates_radial_data {a d ε σ : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hz : z ∈ shearRadialDomain a d ε) :
    |signedShearLogCoordinates σ z 0| = z 0 ∧
    max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) = max (z 1) (z 2) := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  simp [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr,
    Real.exp_log hz.1, Real.exp_log hz.2.1]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.orderedAngularLogCoordinates_radial_data {a d L : ℝ} {z : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hz : z ∈ angularRadialDomain other a d L) :
    |orderedAngularLogCoordinates other z 0| = |z 1| * z 0 ∧
    max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
      (Real.exp (-(orderedAngularLogCoordinates other z) 2)) = z 0 := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho := hz.2.2.2.1
  cases other with
  | false =>
    simp [orderedAngularLogCoordinates, scaledAngularLogCoordinates, abs_mul, abs_of_pos hr,
      Real.exp_log hr, Real.exp_log hz.2.1, max_eq_left ho]
  | true =>
    simp [orderedAngularLogCoordinates, mainWallReflection, scaledAngularLogCoordinates,
      abs_mul, abs_of_pos hr, Real.exp_log hr, Real.exp_log hz.2.1,
      max_eq_right (le_of_lt ho)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPiece_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (i : RadialPieceIndex) : physicalRadialPiece d ε i ⊆ mainWallOpenSection d := by
  rcases i with ⟨neg | other, j⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ha := dyadicScale_pos hd j
    obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha
      (show |(if neg then -1 else 1 : ℝ)| = 1 by cases neg <;> norm_num) hz
    change |signedShearLogCoordinates _ z 0| < d ∧
      max (Real.exp (-(signedShearLogCoordinates _ z) 1))
        (Real.exp (-(signedShearLogCoordinates _ z) 2)) < d
    rw [hs, hm]
    refine ⟨hz.2.2.2.2, (hz.2.2.2.1.trans ?_).trans_lt hz.2.2.2.2⟩
    have hr : 0 < z 0 := ha.trans hz.2.2.1.1
    nlinarith
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other (dyadicScale_pos hd j) hz
    change |orderedAngularLogCoordinates other z 0| < d ∧
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) < d
    rw [hs, hm]
    exact ⟨hz.2.2.2.2.2, hz.2.2.2.2.1⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radialFailurePiece_subset (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : radialFailurePiece d ε F i ⊆ physicalRadialPiece d ε i :=
  image_mono inter_subset_left

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

private theorem BianchiIX.partialCoreReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1} T) : partialCoreReturnTime y = T := hT.csInf_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreReturnTime_eq h

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnState_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnState =ᶠ[𝓝 y] fun z =>
      let out := projectiveOriginalFlow z 0 (τ z)
      ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hτ, partialCoreReturnTime_eventuallyEq hτ] with z hz ht
  simp only [partialCoreReturnState, ht, toCoreAngleState, hz.1.2.2, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialCurve_annulus {r ρ θ ζ L : ℝ} (hr : 0 < r)
    (hρ : ρ ∈ Icc r (2 * r)) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    ‖restartRadialCurve θ ζ ρ‖ ≤ (2 * (L + 1)) * r ∧
      r / 2 ≤ restartRadialNorm (restartRadialCurve θ ζ ρ) := by
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * (L + 1)) * r)).mpr
    intro i
    fin_cases i
    · change |θ * ρ| ≤ _
      rw [abs_mul, abs_of_pos hρ0]
      have H := mul_le_mul hθ hρ.2 hρ0.le hL
      nlinarith only [H, hr]
    · change |ρ| ≤ _
      rw [abs_of_pos hρ0]
      nlinarith only [hρ.2, mul_nonneg hL hr.le]
    · change |ζ| ≤ _
      rw [abs_of_nonneg hζ.1]
      nlinarith only [hζ.2, hr, mul_nonneg hL hr.le]
  · have hdiff : 0 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (θ * ρ)) :
      (ρ - ζ) ^ 2 ≤ (θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    rw [Real.sqrt_sq hdiff] at H
    change r / 2 ≤ Real.sqrt ((θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    linarith only [H, hρ.1, hζ.2, hr]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∀ h ∈ Ioc (0 : ℝ) (1 / (4 * C)),
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Z := restartRadialCurve θ ζ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
            r ≤ 1 ∧ 8 * (L + 1) * r ≤ 1 / 16 ∧ 0 ≤ T ∧
            0 < restartSectionRadicand h Z ∧ T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * r ^ q ∧ ‖p‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
            (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧ p.1 ≤ p.2 1 / 16 ∧ p.2 2 ≤ p.2 1 / 16 ∧
            ‖v‖ ≤ 2 * (L + 1) ∧ |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
            |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, ?_⟩
  intro h hh L hL q hq
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    linarith only [H]
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.1.le]
  let M := 8 * (L + 1)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hL]
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (1 / 64), lt_min hr₀ (by norm_num), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := hr.2.trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ :=
    HC h r T L hh.1 hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left hpower hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hnr : p.1 ≤ r := hnsmall.trans (by nlinarith only [hr.1, Hr.1.1.2])
  have hp : ‖p‖ ≤ M * r := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos hnpos]
    exact ⟨hnr.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM hr.1.le]), hcenter⟩
  have hv : ‖v‖ ≤ 2 * (L + 1) := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    refine ⟨hnv.trans ?_, (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcv⟩
    apply (div_le_iff₀ hr.1).mpr
    exact mul_le_mul_of_nonneg_left hnr (by positivity)
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh.1]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have hcon := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1
  refine ⟨Hr.1.1.2, Hr.1.2.1, hT, hrad, hdom, hcon, hneg, Hcurve, hnpos, hnexp, hp,
    hactive, hweak, ?_, ?_, hv, hnv, hwv⟩
  · nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]
  · have Hw := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
    nlinarith only [Hw, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReturnParameters_eventuallyEq {h s θ ζ ρ : ℝ} {τ : ProjectiveState → ℝ}
    (hY : ContinuousAt (restartFastProjectiveEntry h s θ ζ) ρ)
    (hτ : ∀ᶠ y in 𝓝 (restartFastProjectiveEntry h s θ ζ ρ), IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) :
    restartReturnParameters h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ a) 0
        (τ (restartFastProjectiveEntry h s θ ζ a))
      coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hY.tendsto.eventually (partialCoreReturnState_eventuallyEq hτ)] with a ha
  exact congrArg coreExitConnectionParameters ha

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartReturn_control :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let y := restartFastProjectiveEntry h s θ ζ ρ
            let p := restartReturnParameters h s θ ζ ρ
            let G := restartReturnState h s θ ζ ρ
            let f := restartReturnPhase h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreReturnTime y) ∧
              ContDiffAt ℝ 2 partialCoreReturnTime y ∧ connectionReturnValid p ∧
              1 / (2 * (8 * (L + 1) + 1) * r) ≤ G 0 ∧ G 0 ≤ 64 / r ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 4096 * (8 * (L + 1)) * ζ / r ^ 3 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                  (restartReturnTime h s θ ζ ρ))) ∧
              DifferentiableAt ℝ f ρ ∧ |f ρ - F ρ| ≤ C * r ^ 2 ∧
              |deriv f ρ - deriv F ρ| ≤ C * r ∧
              1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartConnection_output_phase
  obtain ⟨hA, hhA, HA⟩ := exists_restartConnection_output_bounds
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hE (min hA hV), lt_min hhE (lt_min hhA hhV), ?_⟩
  intro h hh L hL
  obtain ⟨C, hC, HCE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HCE q P hq hP
  obtain ⟨rA, hrA, HRA⟩ := HA h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rA (min rV 1)), lt_min hrE (lt_min hrA (lt_min hrV (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrA' := hr.2.trans (min_le_right _ _)
  have hrV' := hrA'.trans (min_le_right _ _)
  have hr1 := hrV'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  obtain ⟨_, hY, _⟩ := HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, _, _, hdf, hval, hder, hlo, hhi⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨S, _, hfirstS, hvalid, hradlo, hradhi, hu, hw, hsum, horbit⟩ :=
    HRA r ⟨hr.1, hrA'.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hvalid hradlo hradhi hu hw hsum horbit
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  have heqTime := partialCoreReturnTime_eventuallyEq hnear
  have ht : partialCoreReturnTime (Y ρ) = T := heqTime.self_of_nhds.trans hτ
  have hp : restartReturnParameters h s θ ζ ρ =
      coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters (toCoreAngleState
      (projectiveOriginalFlow (Y ρ) 0 (partialCoreReturnTime (Y ρ)))) = _
    rw [ht]
  have hg : restartReturnState h s θ ζ ρ =
      connectionReturnPhysicalState (coreExitConnectionParameters
        (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T))) := congrArg connectionReturnPhysicalState hp
  have heq := restartReturnParameters_eventuallyEq hY.continuousAt hnear
  have heqPhase : restartReturnPhase h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (Y a) 0 (τ (Y a))
      2 / connectionReturnPhysicalState
        (coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3]) 0 :=
    heq.mono fun _ ha => congrArg (fun p => 2 / connectionReturnPhysicalState p 0) ha
  dsimp only [s, Y] at ht hp hg heqPhase
  refine ⟨?_, hcτ.congr_of_eventuallyEq heqTime, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hdf.congr_of_eventuallyEq heqPhase, ?_, ?_, ?_, ?_⟩
  · simpa only [ht] using hfirst
  · simpa only [hp] using hvalid
  · simpa only [hg] using hradlo
  · simpa only [hg] using hradhi
  · simpa only [hg] using hu
  · simpa only [hg] using hw
  · simpa only [hg] using hsum
  · simpa only [restartReturnTime, ht, hp, hg] using horbit
  · simpa only [heqPhase.self_of_nhds] using hval
  · simpa only [heqPhase.deriv_eq] using hder
  · simpa only [heqPhase.deriv_eq] using hlo
  · simpa only [heqPhase.deriv_eq] using hhi

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_restartRadial {h θ ζ ρ : ℝ} (hρ : 0 < ρ) (hζ : 0 < ζ) :
    mainWallChart h ![θ * ρ, -Real.log ρ, -Real.log ζ] =
      restartSectionChart h (restartRadialCurve θ ζ ρ) := by
  simp [mainWallChart, mainWallRadicand, restartSectionChart, restartSectionRadicand,
    restartRadialCurve, Real.exp_log hρ, Real.exp_log hζ]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartReturn_reflected_orbit :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
          let T := restartReturnTime h s θ ζ ρ
          let G := restartReturnState h s θ ζ ρ
          y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
            coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
            coreRadiusEntry G = toProjectiveState (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_control
  obtain ⟨C, hC32, HV⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC32
  refine ⟨min hC (1 / (4 * C)), lt_min hhC (by positivity), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨K, _, HK⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨aC, haC, HaC⟩ := HK q P hq hP
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q (by linarith)
  refine ⟨min aC (min aV 1), lt_min haC (lt_min haV zero_lt_one), ?_⟩
  intro a ha θ ζ hθ hζ ρ hρ s y T G
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ a ^ 2 := ⟨hζ.1.le, hζ.2.trans (by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 (by linarith : (2 : ℝ) ≤ P))⟩
  obtain ⟨_, _, hs, hrad, _⟩ := HaV a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨hfirst, _, hvalid, _, _, _, _, _, horbit, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have heq : mainWallChart h y = restartSectionChart h (restartRadialCurve θ ζ ρ) :=
    mainWallChart_restartRadial (ha.1.trans_le hρ.1) hζ.1
  have hy : y ∈ mainWallChartDomain h := by
    change 0 < mainWallRadicand h y
    change 0 < 1 - (θ * ρ) ^ 2 - curvature h ρ ζ at hrad
    simpa [y, mainWallRadicand, Real.exp_log (ha.1.trans_le hρ.1), Real.exp_log hζ.1] using hrad
  have ht : 0 < T := add_pos (add_pos_of_nonneg_of_pos hs hfirst.1.1) hvalid.1.1.1
  have hdom : T ∈ normalizedMaxDomain (mainWallChart h y) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint (mainWallChart_constraint hy) 0 ht.le
  have ho : coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)) := by
    simpa only [heq] using horbit
  refine ⟨hy, ht, hdom, ho, ?_⟩
  rw [normalizedMaxCurve_mainWallReflection hdom, toProjectiveState_axisSwap]
  exact ho

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_restartShear {h τ n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    mainWallChart h ![τ * ρ, -Real.log n₂, -Real.log n₃] =
      restartSectionChart h (restartShearCurve τ n₂ n₃ ρ) := by
  simp [mainWallChart, mainWallRadicand, restartSectionChart, restartSectionRadicand,
    restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallRadicand_restartShear {h τ n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    mainWallRadicand h ![τ * ρ, -Real.log n₂, -Real.log n₃] =
      restartSectionRadicand h (restartShearCurve τ n₂ n₃ ρ) := by
  simp [mainWallRadicand, restartSectionRadicand, restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearAmplitudeBudget_le_of_min {a n₂ n₃ P : ℝ}
    (ha : 0 < a ∧ a ≤ 1) (hP : 4 ≤ P) (h₂ : 0 < n₂ ∧ n₂ ≤ a)
    (h₃ : 0 < n₃ ∧ n₃ ≤ a) (hmin : min n₂ n₃ ≤ a ^ P) :
    0 < restartShearAmplitudeBudget a n₂ n₃ ∧ restartShearAmplitudeBudget a n₂ n₃ ≤ 800 * a := by
  have hp : a ^ P ≤ a ^ (4 : ℕ) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha.2 hP
  have hprod : n₂ * n₃ ≤ a * a ^ 4 := by
    rcases min_le_iff.mp hmin with hsmall | hsmall
    · exact (mul_le_mul (hsmall.trans hp) h₃.2 h₃.1.le (by positivity)).trans_eq (mul_comm _ _)
    · exact mul_le_mul h₂.2 (hsmall.trans hp) h₃.1.le ha.1.le
  refine ⟨by dsimp [restartShearAmplitudeBudget]; positivity [ha.1, h₂.1, h₃.1], ?_⟩
  calc
    _ = 800 * (n₂ * n₃) / a ^ 4 := by unfold restartShearAmplitudeBudget; ring
    _ ≤ 800 * (a * a ^ 4) / a ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity)
    _ = _ := by field_simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_angularRestartData {h s a L P : ℝ} (o : Bool)
    (hT : ∀ p ∈ angularRestartParameterDomain a L P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartReturnTime h s v.1.1 v.1.2 v.2) p)
    (hY : ∀ p ∈ angularRestartParameterDomain a L P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartReturnState h s v.1.1 v.1.2 v.2) p) :
    Measurable ((angularRestartParameterDomain a L P).domRestrict (angularRestartData h s a L o)) := by
  have hTm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hT p hp).continuousAt.continuousWithinAt)).measurable
  have hYm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hY p hp).continuousAt.continuousWithinAt)).measurable
  have hBm : Measurable (fun p : angularRestartParameterDomain a L P => restartAmplitudeBudget L a p.val.1.2) := by
    unfold restartAmplitudeBudget
    fun_prop
  exact (measurable_const.prodMk hTm).prodMk (hBm.prodMk hYm)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.restartAmplitudeBudget_le_scale {L a ζ P : ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (haone : a ≤ 1) (hP : 4 ≤ P) (hζ : ζ ≤ a ^ P) :
    restartAmplitudeBudget L a ζ ≤ 51200 * (L + 1) * a := by
  have hζ4 : ζ ≤ a ^ (4 : ℕ) := hζ.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha haone hP)
  calc
    _ ≤ 6400 * (8 * (L + 1)) * a ^ 4 / a ^ 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hζ4 (by positivity)) (by positivity)
    _ = _ := by field_simp; ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallSmallSection (d : ℝ) : MeasurableSet (mainWallSmallSection d) := by
  have hs : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have hm : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_le hs measurable_const).inter (measurableSet_le hm measurable_const)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_shearRestartData {h s ε a P : ℝ} (o : Bool)
    (hT : ∀ p ∈ shearRestartParameterDomain ε a P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) p)
    (hY : ∀ p ∈ shearRestartParameterDomain ε a P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) p) :
    Measurable ((shearRestartParameterDomain ε a P).domRestrict (shearRestartData h s a o)) := by
  have hTm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hT p hp).continuousAt.continuousWithinAt)).measurable
  have hYm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hY p hp).continuousAt.continuousWithinAt)).measurable
  have hBm : Measurable (fun p : shearRestartParameterDomain ε a P =>
      restartShearAmplitudeBudget a p.val.1.1 p.val.1.2) := by
    unfold restartShearAmplitudeBudget
    fun_prop
  exact (measurable_const.prodMk hTm).prodMk (hBm.prodMk hYm)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialFailureSet_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (F : RadialPieceIndex → Set SectionCoordinates) : radialFailureSet d ε F ⊆ mainWallOpenSection d := by
  rintro z (hb | hp)
  · exact hb.1
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact physicalRadialPiece_subset_openSection hd hε i (radialFailurePiece_subset d ε F i hi)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallOpenSection_subset_small (d : ℝ) : mainWallOpenSection d ⊆ mainWallSmallSection d :=
  fun _ hz => ⟨hz.1.le, hz.2.le⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_mainWallSectionBoundary (d : ℝ) : MeasurableSet (mainWallSectionBoundary d) :=
  (measurableSet_mainWallSmallSection d).diff (measurableSet_mainWallOpenSection d)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_mainWallClosedFailure (d : ℝ) {E : Set SectionCoordinates}
    (hE : MeasurableSet E) : MeasurableSet (mainWallClosedFailure d E) :=
  (measurableSet_mainWallSectionBoundary d).union hE

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallClosedFailure_subset {d : ℝ} {E : Set SectionCoordinates}
    (hE : E ⊆ mainWallOpenSection d) : mainWallClosedFailure d E ⊆ mainWallSmallSection d := by
  rintro z (hb | he)
  · exact hb.1
  · exact mainWallOpenSection_subset_small d (hE he)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallClosedFailure_complement (d : ℝ) (E : Set SectionCoordinates) :
    mainWallSmallSection d \ mainWallClosedFailure d E = mainWallOpenSection d \ E := by
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨by by_contra ho; exact hn (Or.inl ⟨hz, ho⟩), fun he => hn (Or.inr he)⟩
  · rintro ⟨hz, hn⟩
    exact ⟨mainWallOpenSection_subset_small d hz, fun he => he.elim (fun hb => hb.2 hz) hn⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coreRestartWitness_reflected_entry {h T B η σ Bcap : ℝ} {J : ℕ}
    {y : SectionCoordinates} {Z : CoreAngleState} (ht : 0 < T)
    (hdom : T ∈ normalizedMaxDomain (mainWallChart h y) 0)
    (ho : coreRadiusEntry Z = projectiveReflection
      (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)))
    (p : eraSurvivorDomain η J σ Bcap) (hp : p.val = (B, Z))
    (hs : EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p)) (o : Bool) :
    CoreRestartWitness η J σ Bcap (mainWallChart h (if o then mainWallReflection y else y))
      ((if o then 0 else 3, T), (B, Z)) := by
  cases o
  · refine ⟨ht, hdom, p, hp, hs, ?_⟩
    change coreRadiusEntry p.val.2 = toProjectiveState (axisSwap _)
    rw [toProjectiveState_axisSwap, hp]
    exact ho
  · refine ⟨ht, ?_, p, hp, hs, ?_⟩
    · change T ∈ normalizedMaxDomain (mainWallChart h (mainWallReflection y)) 0
      rwa [normalizedMaxDomain_mainWallReflection]
    · change coreRadiusEntry p.val.2 = toProjectiveState
        (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T)
      rw [normalizedMaxCurve_mainWallReflection hdom, toProjectiveState_axisSwap, hp]
      exact ho

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialRestartChart_parameter (k : Bool ⊕ Bool) (z : SectionCoordinates) :
    radialRestartChart k (radialRestartParameter k z) = radialPieceMap k z := by
  rcases k with neg | other
  · cases neg <;> ext i <;> fin_cases i <;>
      simp [radialRestartChart, radialRestartParameter, shearRestartChart, radialPieceMap,
        signedShearLogCoordinates, mainWallReflection]
  · cases other <;> ext i <;> fin_cases i <;>
      simp [radialRestartChart, radialRestartParameter, angularRestartChart, radialPieceMap,
        orderedAngularLogCoordinates, scaledAngularLogCoordinates, mainWallReflection]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialRestartData_output (h q d ε : ℝ) (i : RadialPieceIndex) (z : SectionCoordinates) :
    (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1
      (radialRestartParameter i.1 z)).2 = restartRadialOutput h q d ε i z := by
  rcases i with ⟨neg | other, j⟩ <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialRestartParameter_selected {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i)
    (hn : z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i) :
    radialRestartParameter i.1 z ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1 := by
  have hr : z 0 ∈ Icc (dyadicScale d i.2) (2 * dyadicScale d i.2) := by
    rcases i with ⟨neg | other, j⟩ <;> exact ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
  rcases i with ⟨neg | other, j⟩
  · cases neg <;> exact ⟨by by_contra hl; exact hn ⟨hr, Or.inl hl⟩, hr⟩
  · exact ⟨by by_contra hl; exact hn ⟨hr, Or.inl hl⟩, hr⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartRadialFailure_borel_restart (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ C > (0 : ℝ),
              ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
                ∀ d ∈ Ioc (0 : ℝ) dstar,
                  let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                  let E := radialFailureSet d ε F
                  (∀ i, MeasurableSet (F i)) ∧ MeasurableSet E ∧
                    mainWallOriginalMeasure h E = (∑' i, radialFailureIntegral h d ε F i) ∧
                    mainWallOriginalMeasure h E ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                    mainWallOriginalMeasure h E ≠ ⊤ ∧
                    ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                      ∀ y ∈ mainWallOpenSection d \ E,
                        y ∈ mainWallChartDomain h ∧ (W y).2.1 ≤ Bbound ∧
                        CoreRestartWitness η J σ Bcap (mainWallChart h y) (W y) ∧
                        ∃ i : RadialPieceIndex, y ∈ physicalRadialPiece d ε i ∧
                          (W y).2 = restartRadialOutput h q d ε i (radialPieceInverse i.1 y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartRadialFailure_quantitative hBirkhoff
  obtain ⟨hAR, hhAR, HAR⟩ := exists_restartReturn_joint_regular
  obtain ⟨hSR, hhSR, HSR⟩ := exists_restartShearReturn_common_regular
  obtain ⟨hAO, hhAO, HAO⟩ := exists_restartReturn_reflected_orbit
  obtain ⟨hSO, hhSO, HSO⟩ := exists_restartShearReturn_common_bounds
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hQ, hhQ, hhQ1, HQ⟩ := Hδ η hη hηδ J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, min hQ (min hAR (min hSR (min hAO hSO))),
    lt_min hhQ (lt_min hhAR (lt_min hhSR (lt_min hhAO hhSO))), (min_le_left _ _).trans hhQ1, ?_⟩
  intro h hh q D P hq hD hP ε hε
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  have hh''' := hh''.trans (min_le_right _ _)
  let L := 1 / ε
  have hL : 0 ≤ L := by dsimp only [L]; positivity [hε.1]
  have hP4 : 4 < P := by linarith only [hD, hP]
  obtain ⟨C, hC, dQ, hdQ, hdQh, HDQ⟩ :=
    HQ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP ε hε
  obtain ⟨aAR, haAR, HAReg⟩ := HAR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ L hL q P hq hP4
  obtain ⟨aSR, haSR, HSReg⟩ := HSR h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aAO, haAO, HAOrbit⟩ := HAO h ⟨hh.1, hh'''.trans (min_le_left _ _)⟩ L hL q P hq hP4
  obtain ⟨aSO, haSO, HSOrbit⟩ := HSO h ⟨hh.1, hh'''.trans (min_le_right _ _)⟩ q D P hq hD hP
  let K := 51200 * (L + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨C, hC, ?_⟩
  intro Bbound hBbound
  let d₀ := min dQ (min aAR (min aSR (min aAO aSO)))
  refine ⟨min d₀ (min 1 (min (Bbound / 800) (Bbound / K))),
    lt_min (lt_min hdQ (lt_min haAR (lt_min haSR (lt_min haAO haSO))))
      (lt_min zero_lt_one (lt_min (div_pos hBbound (by norm_num)) (div_pos hBbound hK))),
    ((min_le_left _ _).trans (min_le_left _ _)).trans hdQh, ?_⟩
  intro d hd F E
  have hd₀ : d ≤ d₀ := hd.2.trans (min_le_left _ _)
  have hd' := hd₀.trans (min_le_right _ _)
  have hd'' := hd'.trans (min_le_right _ _)
  have hd''' := hd''.trans (min_le_right _ _)
  have hdnum := hd.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := hd.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSd : 800 * d ≤ Bbound := by
    have H := (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp (hdnum.trans (min_le_left _ _))
    nlinarith only [H]
  have hAd : K * d ≤ Bbound := by
    have H := (le_div_iff₀ hK).mp (hdnum.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨hF, hE, Heq, Hbound, Hfin, _, Hstats⟩ := HDQ d ⟨hd.1, hd₀.trans (min_le_left _ _)⟩
  have hdata (i : RadialPieceIndex) : Measurable
      ((radialRestartParameterDomain (dyadicScale d i.2) ε P i.1).domRestrict
        (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1)) := by
    rcases i with ⟨neg | other, j⟩
    · have H (v : (ℝ × ℝ) × ℝ) (hv : v ∈ shearRestartParameterDomain ε (dyadicScale d j) P) :=
        HSReg (dyadicScale d j) ⟨dyadicScale_pos hd.1 j,
          (dyadicScale_le hd.1.le j).trans (hd''.trans (min_le_left _ _))⟩
          ε v.1.1 v.1.2 ⟨hε.1.le, hε.2⟩ hv.1.1 hv.1.2.1 hv.1.2.2 v.2 hv.2
      exact measurable_shearRestartData neg (fun v hv => (H v hv).2.2.2) (fun v hv => (H v hv).2.1)
    · have H (v : (ℝ × ℝ) × ℝ) (hv : v ∈ angularRestartParameterDomain (dyadicScale d j) L P) :=
        HAReg (dyadicScale d j) ⟨dyadicScale_pos hd.1 j,
          (dyadicScale_le hd.1.le j).trans (hd'.trans (min_le_left _ _))⟩ v.1.1 v.1.2 hv.1.1 hv.1.2 v.2 hv.2
      exact measurable_angularRestartData other (fun v hv => (H v hv).2.2.2.2) (fun v hv => (H v hv).2.2.1)
  have Hpoint (i : RadialPieceIndex) (v : (ℝ × ℝ) × ℝ)
      (hv : v ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1)
      (p : eraSurvivorDomain η J σ Bcap)
      (hp : p.val = (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2))
        (dyadicScale d i.2) ε i.1 v).2)
      (hs : EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p)) :
      radialRestartChart i.1 v ∈ mainWallChartDomain h ∧
      (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1 v).2.1 ≤ Bbound ∧
      CoreRestartWitness η J σ Bcap (mainWallChart h (radialRestartChart i.1 v))
        (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1 v) := by
    rcases i with ⟨neg | other, j⟩
    · have ha := dyadicScale_pos hd.1 j
      have had := dyadicScale_le hd.1.le j
      have hweak : 2 * ε * dyadicScale d j ≤ dyadicScale d j :=
        mul_le_of_le_one_left ha.le (by linarith only [hε.2])
      have hb := (restartShearAmplitudeBudget_le_of_min ⟨ha, had.trans hd1⟩ hP4.le
        ⟨hv.1.1.1, hv.1.1.2.trans hweak⟩ ⟨hv.1.2.1.1, hv.1.2.1.2.trans hweak⟩ hv.1.2.2).2.trans
          ((mul_le_mul_of_nonneg_left had (by norm_num : (0 : ℝ) ≤ 800)).trans hSd)
      obtain ⟨hrad, htime, ht, hdom, _, _, _, _, _, _, ho⟩ := HSOrbit (dyadicScale d j)
        ⟨ha, had.trans (hd'''.trans (min_le_right _ _))⟩ ε v.1.1 v.1.2 ⟨hε.1.le, hε.2⟩
        hv.1.1 hv.1.2.1 hv.1.2.2 v.2 hv.2
      rw [← mainWallRadicand_restartShear hv.1.1.1 hv.1.2.1.1, one_mul] at hrad
      rw [← mainWallChart_restartShear hv.1.1.1 hv.1.2.1.1, one_mul] at hdom ho
      refine ⟨?_, hb, coreRestartWitness_reflected_entry (htime.trans_lt ht) hdom ho p hp hs neg⟩
      cases neg
      · exact hrad
      · simpa only [radialRestartChart, shearRestartChart, ite_true, mainWallChartDomain,
          mem_ofPred_eq, mainWallRadicand_reflection] using hrad
    · have ha := dyadicScale_pos hd.1 j
      have had := dyadicScale_le hd.1.le j
      have hb := (restartAmplitudeBudget_le_scale hL ha (had.trans hd1) hP4.le hv.1.2.2).trans
        ((mul_le_mul_of_nonneg_left had hK.le).trans hAd)
      obtain ⟨hy, ht, hdom, ho, _⟩ := HAOrbit (dyadicScale d j)
        ⟨ha, had.trans (hd'''.trans (min_le_left _ _))⟩ v.1.1 v.1.2 hv.1.1 hv.1.2 v.2 hv.2
      refine ⟨?_, hb, coreRestartWitness_reflected_entry ht hdom ho p hp hs other⟩
      cases other
      · exact hy
      · simpa only [radialRestartChart, angularRestartChart, ite_true, mainWallChartDomain,
          mem_ofPred_eq, mainWallRadicand_reflection] using hy
  obtain ⟨W, hW, HW⟩ := exists_measurable_radial_restart hd.1 hε.1 (by linarith only [hε.2]) hF hdata
  refine ⟨hF, hE, Heq, Hbound, Hfin, W, hW, ?_⟩
  intro y hy
  obtain ⟨i, z, hz, hn, heq, hval⟩ := HW y hy
  obtain ⟨p, hp, hs⟩ := Hstats i z hz hn
  have H := Hpoint i (radialRestartParameter i.1 z) (radialRestartParameter_selected hz hn)
    p (hp.trans (radialRestartData_output h q d ε i z).symm) hs
  rw [radialRestartChart_parameter, heq, ← hval] at H
  refine ⟨H.1, H.2.1, H.2.2, i, ⟨z, hz, heq⟩, ?_⟩
  rw [hval, radialRestartData_output, ← heq, radialPieceInverse_map hd.1 hz]

end
end

/-- The closed-section formulation adds a null boundary, with exactly the same successful target and flux. -/
theorem solution (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ C > (0 : ℝ),
              ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
                ∀ d ∈ Ioc (0 : ℝ) dstar,
                  let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                  let E := mainWallClosedFailure d (radialFailureSet d ε F)
                  MeasurableSet E ∧ E ⊆ mainWallSmallSection d ∧
                    mainWallOriginalMeasure h E = (∑' i, radialFailureIntegral h d ε F i) ∧
                    mainWallMeasure h E ≤ mainWallOriginalMeasure h E ∧
                    mainWallOriginalMeasure h E ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                    mainWallOriginalMeasure h E ≠ ⊤ ∧
                    ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                      ∀ y ∈ mainWallSmallSection d \ E,
                        y ∈ mainWallChartDomain h ∧ (W y).2.1 ≤ Bbound ∧
                        CoreRestartWitness η J σ Bcap (mainWallChart h y) (W y) ∧
                        ∃ i : RadialPieceIndex, y ∈ physicalRadialPiece d ε i ∧
                          (W y).2 = restartRadialOutput h q d ε i (radialPieceInverse i.1 y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartRadialFailure_borel_restart hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hstar, hhstar, hh1, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, hstar, hhstar, hh1, ?_⟩
  intro h hh q D P hq hD hP ε hε
  obtain ⟨C, hC, HC⟩ := HH h hh q D P hq hD hP ε hε
  refine ⟨C, hC, ?_⟩
  intro Bbound hBbound
  obtain ⟨dstar, hdstar, hdh, HD⟩ := HC Bbound hBbound
  refine ⟨dstar, hdstar, hdh, ?_⟩
  intro d hd F E
  obtain ⟨_, hF, Heq, Hbound, Hfin, W, hW, HW⟩ := HD d hd
  have hmeasure : mainWallOriginalMeasure h E = mainWallOriginalMeasure h (radialFailureSet d ε F) :=
    mainWallOriginalMeasure_closedFailure h d _
  refine ⟨measurableSet_mainWallClosedFailure d hF,
    mainWallClosedFailure_subset (radialFailureSet_subset_openSection hd.1 (by linarith only [hε.2]) F),
    hmeasure.trans Heq, mainWallMeasure_le_original hh.1 E,
    hmeasure.trans_le Hbound, hmeasure ▸ Hfin, W, hW, ?_⟩
  intro y hy
  exact HW y (by rwa [mainWallClosedFailure_complement] at hy)
