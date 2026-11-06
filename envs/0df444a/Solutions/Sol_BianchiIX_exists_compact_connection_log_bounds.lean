-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:59:48.665882+00:00
-- url     : https://prove2.me/submissions/ed3f82f9-7206-4cb5-b70e-1741c3886ba4

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Definitions.Def_BianchiIX_TerminalConnectionData
import Theorems.Thm_BianchiIX_compact_log_composition_bounds
import Theorems.Thm_BianchiIX_coreTail_reflected_multiplier_state
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entranceReturn_walls_pos
import Theorems.Thm_BianchiIX_exists_compact_connection_entrance_data
import Theorems.Thm_BianchiIX_exists_compact_connection_tangent_bounds
import Theorems.Thm_BianchiIX_exists_entrance_return_full_columns
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.compactConnectionCoordinates_eq {η : ℝ} {Y : CoreAngleState} (H : coreTailValid η Y) :
    compactConnectionCoordinates η Y = entranceRadialCoordinates (compactConnectionEntry η Y) := by
  have heq := coreTail_reflected_multiplier_state H
  ext i
  fin_cases i
  · rfl
  · exact (congrFun heq 1).symm
  · exact (congrFun heq 2).symm
  · exact (congrFun heq 3).symm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasFDerivAt_entranceLogWalls {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) :
    HasFDerivAt (entranceLogWalls k)
      (ContinuousLinearMap.pi (![(y 1)⁻¹ • ContinuousLinearMap.proj 1,
        k ^ 2 • ((y 3)⁻¹ • ContinuousLinearMap.proj 3)] : Fin 2 → (ProjectiveState →L[ℝ] ℝ))) y := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).log hu
  · exact ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).log hw).const_mul (k ^ 2)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.EntranceRadialInverseAt.hasFDerivAt_return {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    HasFDerivAt (fun z => entranceReturnState (Ψ z))
      ((fderiv ℝ entranceReturnState y).comp (entranceRadialInverseDifferential y)) (entranceRadialCoordinates y) := by
  have hd : HasFDerivAt entranceReturnState (fderiv ℝ entranceReturnState y) (Ψ (entranceRadialCoordinates y)) := by
    rw [HΨ.apply_base]
    exact ((entranceReturn_regular hk hm hu hv hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [Function.comp_def] using hd.comp (entranceRadialCoordinates y) HΨ.hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.compactConnectionLogWalls_chart_germ {η : ℝ} {Y : CoreAngleState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (compactConnectionEntry η Y) Ψ)
    (hentry : ContinuousAt (compactConnectionEntry η) Y)
    (hvalid : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z) :
    compactConnectionLogWalls η =ᶠ[𝓝 Y] (fun Z =>
      entranceLogWalls 1 (entranceReturnState (Ψ (compactConnectionCoordinates η Z)))) := by
  filter_upwards [hentry.tendsto.eventually HΨ.left_inverse, hvalid] with Z hz hv
  rw [compactConnectionCoordinates_eq hv, hz]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.compactConnectionLogWalls_differential {η : ℝ} {Y : CoreAngleState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (compactConnectionEntry η Y) Ψ)
    (hentry : ContinuousAt (compactConnectionEntry η) Y)
    (hvalid : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z)
    (hc : DifferentiableAt ℝ (compactConnectionCoordinates η) Y)
    (hL : DifferentiableAt ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
      (entranceRadialCoordinates (compactConnectionEntry η Y))) :
    DifferentiableAt ℝ (compactConnectionLogWalls η) Y ∧ ∀ v : CoreAngleState,
      fderiv ℝ (compactConnectionLogWalls η) Y v =
        fderiv ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
          (compactConnectionCoordinates η Y) (fderiv ℝ (compactConnectionCoordinates η) Y v) := by
  have heq := compactConnectionLogWalls_chart_germ HΨ hentry hvalid
  have hbase := compactConnectionCoordinates_eq hvalid.self_of_nhds
  have hL' : DifferentiableAt ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
      (compactConnectionCoordinates η Y) := by rw [hbase]; exact hL
  have hd := hL'.hasFDerivAt.comp Y hc.hasFDerivAt
  refine ⟨hd.differentiableAt.congr_of_eventuallyEq heq, ?_⟩
  intro v
  rw [heq.fderiv_eq]
  exact congrArg (fun L : CoreAngleState →L[ℝ] (Fin 2 → ℝ) => L v) hd.fderiv

end
end


/-- The actual compact connection has the logarithmic cone bounds used before B.52. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        DifferentiableAt ℝ (compactConnectionLogWalls η) Y ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        |fderiv ℝ (compactConnectionLogWalls η) Y v 0| ≤
          C * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 1) + 1 / Real.sqrt (Y 2)) ∧
        |fderiv ℝ (compactConnectionLogWalls η) Y v 1| ≤
          C * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 2)) := by
  obtain ⟨B, hB, δ, hδ, hδsmall, HB⟩ := exists_entrance_return_full_columns
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εt, hεt, A, hA, HT⟩ := exists_compact_connection_tangent_bounds ⟨hη.1, hη.2.trans hδsmall⟩
  obtain ⟨εe, hεe, _, _, HE⟩ := exists_compact_connection_entrance_data ⟨hδ, hδsmall⟩ hη
  let ε := min εt εe
  have hεt' : ε ≤ εt := min_le_left _ _
  have hεe' : ε ≤ εe := min_le_right _ _
  have hA0 : 0 ≤ A := by linarith only [hA]
  refine ⟨ε, lt_min hεt hεe, B * A ^ 2 + 6 * (B * A) + A + 4 * B + 1, by positivity, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, _, hentry, hrange, hm, hU, hV, hW, _, _⟩ := HE Y hk
    ⟨hu.1, hu.2.trans hεe'⟩ ⟨hw.1, hw.2.trans hεe'⟩
  obtain ⟨hvalid, hc, hlog, HD⟩ := HT Y hk ⟨hu.1, hu.2.trans hεt'⟩ ⟨hw.1, hw.2.trans hεt'⟩
  let y := compactConnectionEntry η Y
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨hV.1, by linarith only [hV.2]⟩
  have hww : 0 < y 3 ∧ y 3 ≤ δ := by
    change 0 < compactConnectionEntry η Y 3 ∧ compactConnectionEntry η Y 3 ≤ δ
    rw [hW]
    exact hη
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hU.1.le, hU.2.trans hδsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hww.1.le, hww.2.trans hδsmall⟩
  obtain ⟨Ψ, HΨ, _, HU, HW⟩ := HB y 1 hrange.1 hm hU hv hww (Or.inl rfl)
  let F := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let z := compactConnectionCoordinates η Y
  have hbase : z = entranceRadialCoordinates y := compactConnectionCoordinates_eq htail
  have hzu : z 1 = y 1 := congrFun hbase 1
  have hzv : z 2 = y 2 := congrFun hbase 2
  have HR := entranceReturn_regular hrange.1 hm hu' hv hw'
  have hpos := entranceReturn_walls_pos hrange.1 hm ⟨hU.1, hu'.2⟩ hv ⟨hww.1, hw'.2⟩
    (entranceReturnTime y) ⟨HR.1.1.1.1.le, le_rfl⟩
  have hLp : DifferentiableAt ℝ (entranceLogWalls 1) (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact (hasFDerivAt_entranceLogWalls 1 hpos.1.ne' hpos.2.2.ne').differentiableAt
  have hLf : DifferentiableAt ℝ F (entranceRadialCoordinates y) :=
    hLp.comp (entranceRadialCoordinates y) (g := entranceLogWalls 1)
      (f := fun z => entranceReturnState (Ψ z)) (HΨ.hasFDerivAt_return hrange.1 hm hu' hv hw').differentiableAt
  have Hdiff := compactConnectionLogWalls_differential HΨ hentry.continuousAt hvalid
    (hc.differentiableAt (by norm_num)) hLf
  refine ⟨htail, HR.1, Hdiff.1, ?_⟩
  intro v hv0 hv1 hv2
  obtain ⟨hd0, hd1, hdu, hdv, hd3⟩ := HD v hv0 hv1 hv2
  let J := fderiv ℝ F z
  let d := fderiv ℝ (compactConnectionCoordinates η) Y v
  have hk2 : 1 ≤ coreRadius (y 0) (y 2) ^ 2 := by nlinarith only [hrange.1]
  have hL0 : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have HUr : |J (Pi.single 0 1) 0| ≤ B * (-Real.log (y 2)) := by
    change |fderiv ℝ F z (Pi.single 0 1) 0| ≤ _
    rw [hbase]
    exact HU.1
  have HUu : |J (Pi.single 1 1) 0 - 1 / y 1| ≤ B := by
    change |fderiv ℝ F z (Pi.single 1 1) 0 - 1 / y 1| ≤ _
    rw [hbase]
    exact HU.2.1
  have HUv : |J (Pi.single 2 1) 0| ≤ 4 * B / y 2 := by
    change |fderiv ℝ F z (Pi.single 2 1) 0| ≤ _
    rw [hbase]
    exact HU.2.2.1.trans (div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hrange.2.le hB.le]) hv.1.le)
  have HWr : |J (Pi.single 0 1) 1| ≤ B * (-Real.log (y 2)) := by
    change |fderiv ℝ F z (Pi.single 0 1) 1| ≤ _
    rw [hbase]
    exact HW.1.trans (div_le_self (mul_nonneg hB.le hL0) hk2)
  have HWu : |J (Pi.single 1 1) 1| ≤ B := by
    change |fderiv ℝ F z (Pi.single 1 1) 1| ≤ _
    rw [hbase]
    exact HW.2.1.trans (div_le_self hB.le hk2)
  have HWv : |J (Pi.single 2 1) 1| ≤ B / y 2 := by
    change |fderiv ℝ F z (Pi.single 2 1) 1| ≤ _
    rw [hbase]
    exact HW.2.2.1
  change -Real.log (z 2) ≤ _ at hlog
  change |d 1| ≤ z 1 * _ at hdu
  change |d 2| ≤ z 2 * _ at hdv
  rw [hzv] at hlog hdv
  rw [hzu] at hdu
  have H := compact_log_composition_bounds J d hA0 hB.le hU.1 hv.1 (abs_nonneg _)
    (by positivity [hu.1] : 0 ≤ 1 / Real.sqrt (Y 1)) (by positivity [hw.1] : 0 ≤ 1 / Real.sqrt (Y 2))
    hlog hd0 hd1 hdu hdv hd3 HUr HUu HUv HWr HWu HWv
  rw [Hdiff.2 v]
  exact H
