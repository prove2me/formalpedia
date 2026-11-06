-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_weighted_wall_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:01:34.689619+00:00
-- url     : https://prove2.me/submissions/12ec735a-266d-43bf-8f25-39084478e5ec

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Definitions.Def_BianchiIX_TerminalConnectionData
import Theorems.Thm_BianchiIX_exists_compact_connection_log_bounds
import Theorems.Thm_BianchiIX_exists_compact_connection_return
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
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_log_small_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.sqrt x * (1 + |Real.log x|) ≤ 2 := by
  have hs := Real.sqrt_pos.mpr hx
  have H := Real.one_sub_inv_le_log_of_pos hs
  rw [Real.log_sqrt hx.le] at H
  have H' := mul_le_mul_of_nonneg_left H hs.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hs.ne'] at H'
  rw [abs_of_nonpos (Real.log_nonpos hx.le hx1)]
  nlinarith only [H', hs.le]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.compact_strong_cone_power {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.sqrt x * y ^ (19 / 24 : ℝ) *
      (1 + |Real.log y| + 1 / Real.sqrt x + 1 / Real.sqrt y) ≤ 4 * (x + y) ^ (19 / 24 : ℝ) := by
  have hb : 0 < x + y := add_pos hx hy
  have hsplit : y ^ (19 / 24 : ℝ) = y ^ (7 / 24 : ℝ) * Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy]
    norm_num
  have hprod : Real.sqrt x * y ^ (7 / 24 : ℝ) ≤ (x + y) ^ (19 / 24 : ℝ) := by
    calc
      _ ≤ Real.sqrt (x + y) * (x + y) ^ (7 / 24 : ℝ) := mul_le_mul
        (Real.sqrt_le_sqrt (by linarith only [hy]))
        (Real.rpow_le_rpow hy.le (by linarith only [hx]) (by norm_num))
        (Real.rpow_nonneg hy.le _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]; norm_num
  have hself : y ^ (19 / 24 : ℝ) ≤ (x + y) ^ (19 / 24 : ℝ) :=
    Real.rpow_le_rpow hy.le (by linarith only [hx]) (by norm_num)
  have hid : Real.sqrt x * y ^ (19 / 24 : ℝ) *
      (1 + |Real.log y| + 1 / Real.sqrt x + 1 / Real.sqrt y) =
      (Real.sqrt x * y ^ (7 / 24 : ℝ)) * (Real.sqrt y * (1 + |Real.log y|)) +
        y ^ (19 / 24 : ℝ) + Real.sqrt x * y ^ (7 / 24 : ℝ) := by
    rw [hsplit]
    field_simp [(Real.sqrt_pos.mpr hx).ne', (Real.sqrt_pos.mpr hy).ne']
  rw [hid]
  have H := mul_le_mul_of_nonneg_left (sqrt_log_small_bound hy hy1)
    (mul_nonneg (Real.sqrt_nonneg x) (Real.rpow_nonneg hy.le (7 / 24)))
  nlinarith only [H, hprod, hself]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.compact_weak_cone_power {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hy1 : y ≤ 1) :
    y ^ (13 / 18 : ℝ) * (1 + |Real.log y| + 1 / Real.sqrt y) ≤ 3 * (x + y) ^ (2 / 9 : ℝ) := by
  have hsplit : y ^ (13 / 18 : ℝ) = y ^ (2 / 9 : ℝ) * Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy]
    norm_num
  have hid : y ^ (13 / 18 : ℝ) * (1 + |Real.log y| + 1 / Real.sqrt y) =
      y ^ (2 / 9 : ℝ) * (Real.sqrt y * (1 + |Real.log y|)) + y ^ (2 / 9 : ℝ) := by
    rw [hsplit]
    field_simp [(Real.sqrt_pos.mpr hy).ne']
  rw [hid]
  have H := mul_le_mul_of_nonneg_left (sqrt_log_small_bound hy hy1) (Real.rpow_nonneg hy.le (2 / 9))
  have Hp := Real.rpow_le_rpow hy.le (show y ≤ x + y by linarith only [hx]) (by norm_num : (0 : ℝ) ≤ 2 / 9)
  linarith only [H, Hp]

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
open Set MeasureTheory

private theorem BianchiIX.entranceLogWalls_fderiv_apply {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (entranceLogWalls k) y v = entranceWallTangent k y v := by
  rw [(hasFDerivAt_entranceLogWalls k hu hw).fderiv]
  ext i
  fin_cases i <;> simp [entranceWallTangent, div_eq_mul_inv, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.compactConnectionLogWalls_fderiv {η : ℝ} {Y : CoreAngleState}
    (hstate : DifferentiableAt ℝ (compactConnectionState η) Y)
    (hu : compactConnectionState η Y 1 ≠ 0) (hw : compactConnectionState η Y 3 ≠ 0)
    (v : CoreAngleState) :
    fderiv ℝ (compactConnectionLogWalls η) Y v =
      ![fderiv ℝ (compactConnectionState η) Y v 1 / compactConnectionState η Y 1,
        fderiv ℝ (compactConnectionState η) Y v 3 / compactConnectionState η Y 3] := by
  have hd := (hasFDerivAt_entranceLogWalls 1 hu hw).differentiableAt.hasFDerivAt.comp Y hstate.hasFDerivAt
  change fderiv ℝ (entranceLogWalls 1 ∘ compactConnectionState η) Y v = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply 1 hu hw]
  simp only [entranceWallTangent, one_pow, one_mul]

end
end


/-- B.52 and the stronger strong-wall exponent, before division by the outgoing phase derivative. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionState η) Y ∧
        0 < compactConnectionState η Y 1 ∧ 0 < compactConnectionState η Y 3 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        |fderiv ℝ (compactConnectionState η) Y v 1| ≤
          C * (Y 1 + Y 2) ^ (19 / 24 : ℝ) * Real.sqrt (compactConnectionState η Y 1) ∧
        |fderiv ℝ (compactConnectionState η) Y v 3| ≤
          C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 3) := by
  obtain ⟨δ, hδ, hδsmall, HL⟩ := exists_compact_connection_log_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εl, hεl, B, hB, HL'⟩ := HL η hη
  obtain ⟨εa, hεa, A, hA, HA⟩ := exists_compact_connection_return ⟨hη.1, hη.2.trans hδsmall⟩
  let ε := min εl (min εa 1)
  have hεl' : ε ≤ εl := min_le_left _ _
  have hεa' : ε ≤ εa := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, lt_min hεl (lt_min hεa zero_lt_one), 4 * Real.sqrt A * B, by positivity, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, hreturn, _, hstate, _, _, _, _, hU, hW⟩ := HA Y hk
    ⟨hu.1, hu.2.trans hεa'⟩ ⟨hw.1, hw.2.trans hεa'⟩
  obtain ⟨_, _, _, HLogs⟩ := HL' Y hk ⟨hu.1, hu.2.trans hεl'⟩ ⟨hw.1, hw.2.trans hεl'⟩
  have hsu : Real.sqrt (compactConnectionState η Y 1) ≤
      Real.sqrt A * Real.sqrt (Y 1) * (Y 2) ^ (19 / 24 : ℝ) := by
    have H := Real.sqrt_le_sqrt hU.2.1
    rw [Real.sqrt_mul (mul_nonneg hA.le hu.1.le), Real.sqrt_mul hA.le,
      Real.sqrt_eq_rpow ((Y 2) ^ (19 / 12 : ℝ)), ← Real.rpow_mul hw.1.le] at H
    norm_num at H
    exact H
  have hsw : Real.sqrt (compactConnectionState η Y 3) ≤ Real.sqrt A * (Y 2) ^ (13 / 18 : ℝ) := by
    have H := Real.sqrt_le_sqrt hW.2.1
    rw [Real.sqrt_mul hA.le, Real.sqrt_eq_rpow ((Y 2) ^ (13 / 9 : ℝ)), ← Real.rpow_mul hw.1.le] at H
    norm_num at H
    exact H
  refine ⟨htail, hreturn, hstate, hU.1, hW.1, ?_⟩
  intro v hv0 hv1 hv2
  obtain ⟨Hlu, Hlw⟩ := HLogs v hv0 hv1 hv2
  let L := fderiv ℝ (compactConnectionLogWalls η) Y v
  have HcoefU : Real.sqrt (compactConnectionState η Y 1) * |L 0| ≤
      (4 * Real.sqrt A * B) * (Y 1 + Y 2) ^ (19 / 24 : ℝ) := by
    calc
      _ ≤ (Real.sqrt A * Real.sqrt (Y 1) * (Y 2) ^ (19 / 24 : ℝ)) *
          (B * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 1) + 1 / Real.sqrt (Y 2))) :=
        mul_le_mul hsu Hlu (abs_nonneg _) (by positivity [hu.1, hw.1])
      _ = (Real.sqrt A * B) * (Real.sqrt (Y 1) * (Y 2) ^ (19 / 24 : ℝ) *
          (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 1) + 1 / Real.sqrt (Y 2))) := by ring
      _ ≤ (Real.sqrt A * B) * (4 * (Y 1 + Y 2) ^ (19 / 24 : ℝ)) :=
        mul_le_mul_of_nonneg_left (compact_strong_cone_power hu.1 hw.1 (hw.2.trans hε1)) (by positivity)
      _ = _ := by ring
  have HcoefW : Real.sqrt (compactConnectionState η Y 3) * |L 1| ≤
      (4 * Real.sqrt A * B) * (Y 1 + Y 2) ^ (2 / 9 : ℝ) := by
    calc
      _ ≤ (Real.sqrt A * (Y 2) ^ (13 / 18 : ℝ)) *
          (B * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 2))) :=
        mul_le_mul hsw Hlw (abs_nonneg _) (by positivity [hw.1])
      _ = (Real.sqrt A * B) * ((Y 2) ^ (13 / 18 : ℝ) * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 2))) := by ring
      _ ≤ (Real.sqrt A * B) * (3 * (Y 1 + Y 2) ^ (2 / 9 : ℝ)) :=
        mul_le_mul_of_nonneg_left (compact_weak_cone_power hu.1.le hw.1 (hw.2.trans hε1)) (by positivity)
      _ ≤ _ := by
        have H := mul_nonneg (mul_nonneg (Real.sqrt_nonneg A) hB.le)
          (Real.rpow_nonneg (add_nonneg hu.1.le hw.1.le) (2 / 9))
        nlinarith only [H]
  have HD := compactConnectionLogWalls_fderiv (hstate.differentiableAt (by norm_num)) hU.1.ne' hW.1.ne' v
  have huD : fderiv ℝ (compactConnectionState η) Y v 1 = compactConnectionState η Y 1 * L 0 := by
    have H := congrFun HD 0
    change L 0 = _ / _ at H
    rw [H]
    field_simp [hU.1.ne']
  have hwD : fderiv ℝ (compactConnectionState η) Y v 3 = compactConnectionState η Y 3 * L 1 := by
    have H := congrFun HD 1
    change L 1 = _ / _ at H
    rw [H]
    field_simp [hW.1.ne']
  constructor
  · rw [huD, abs_mul, abs_of_pos hU.1]
    have H := mul_le_mul_of_nonneg_left HcoefU (Real.sqrt_nonneg (compactConnectionState η Y 1))
    rw [← mul_assoc, Real.mul_self_sqrt hU.1.le] at H
    simpa only [mul_comm] using H
  · rw [hwD, abs_mul, abs_of_pos hW.1]
    have H := mul_le_mul_of_nonneg_left HcoefW (Real.sqrt_nonneg (compactConnectionState η Y 3))
    rw [← mul_assoc, Real.mul_self_sqrt hW.1.le] at H
    simpa only [mul_comm] using H
