-- Prove2me | solution 1 for BianchiIX.coreRadiusEntry_field_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:57:13.293343+00:00
-- url     : https://prove2.me/submissions/35bf0e8b-7e20-4694-9da7-74671594a50b

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreAuxiliary_coefficient_bounds
import Theorems.Thm_BianchiIX_core_radial_velocity_bound
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

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreAngleField_radius_projective {y : ProjectiveState} (hv : 0 < y 2) :
    coreAngleField (coreAngle (y 0) (y 2)) (toCoreAngleState y) 0 =
      (-coupling (y 1) (y 2) (y 3) - Real.tanh (coreAngle (y 0) (y 2)) * (y 1 - y 3) ^ 2 /
        coreRadius (y 0) (y 2)) / coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change (-coupling (y 1) (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) -
      Real.tanh (coreAngle (y 0) (y 2)) *
        (y 1 - y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) ^ 2 /
          coreRadius (y 0) (y 2)) /
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
        (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.toCoreAngleState_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    toCoreAngleState (coreRadiusEntry Y) = Y := by
  ext i
  fin_cases i
  · exact coreRadius_coreRadiusEntry hk
  · rfl
  · simp [toCoreAngleState, coreRadiusEntry]

end
end

theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    let f := coreAngleField (projectiveCoreAngle (coreRadiusEntry Y)) Y
    |f 0| ≤ 2 * (Y 1 + Y 2 ^ 2 / Y 0) ∧
      |f 1| ≤ 2 * Y 0 * Y 1 ∧ |f 2| ≤ 4 * Y 2 / Y 0 := by
  intro f
  let k := Y 0
  let u := Y 1
  let w := Y 2
  let z := projectiveCoreAngle (coreRadiusEntry Y)
  let q := coreAuxiliary z Y
  have hk0 : 0 < k := by dsimp [k]; linarith only [hk]
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have hr : 99 / 100 * k ≤ Y 0 ∧ Y 0 ≤ 101 / 100 * k := by dsimp [k]; constructor <;> linarith only [hk]
  have hv : 0 < coreRadiusEntry Y 2 := by change (0 : ℝ) < 1; norm_num
  have hV : Y 0 / Real.cosh z = 1 := by
    have H := (coreAngle_coordinates (m := coreRadiusEntry Y 0) hv).1
    rw [coreRadius_coreRadiusEntry hk1] at H
    exact H
  obtain ⟨hC, ha, _, hd, _⟩ := coreAuxiliary_coefficient_bounds hk hr
    (by rw [hV]) hu (by simpa only [hV, div_one] using hw)
  change 0 ≤ q 0 ∧ q 0 ≤ 1 / 100 at hC
  change |q 2| ≤ k at ha
  change 999 / 1000 ≤ q 1 at hd
  have hd0 : 0 < q 1 := by linarith only [hd]
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have huw : u * w ≤ u / 4 := by
    have H := mul_le_mul_of_nonneg_left hw' hu.1
    change u * w ≤ u * (1 / 60000) at H
    nlinarith only [H, hu.1]
  have huu : u ^ 2 / k ≤ u / 4 := by
    have H := mul_le_mul_of_nonneg_left hu' hu.1
    exact (div_le_self (sq_nonneg u) (by dsimp [k]; linarith only [hk])).trans
      (by change u * u ≤ u * (1 / 60000) at H; nlinarith only [H, hu.1])
  have hf0 : f 0 = (-coupling u 1 w - Real.tanh z * (u - w) ^ 2 / k) / coreClockFactor k u w := by
    have H := coreAngleField_radius_projective hv
    rw [toCoreAngleState_coreRadiusEntry hk1, coreRadius_coreRadiusEntry hk1] at H
    exact H
  refine ⟨?_, ?_, ?_⟩
  · rw [hf0]
    have H := core_radial_velocity_bound hk hr.1 (v := 1) le_rfl hu hw (Real.abs_tanh_lt_one z).le
    apply H.trans
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
    change u * 1 + u * w + u ^ 2 / k + w ^ 2 / k ≤ _
    nlinarith only [huw, huu, hu.1, div_nonneg (sq_nonneg w) hk0.le]
  · change |u * q 2 / q 1| ≤ 2 * k * u
    rw [abs_div, abs_mul, abs_of_nonneg hu.1, abs_of_pos hd0]
    calc
      u * |q 2| / q 1 ≤ u * k / q 1 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha hu.1) hd0.le
      _ ≤ 2 * k * u := (div_le_iff₀ hd0).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hd (mul_nonneg hk0.le hu.1), mul_nonneg hk0.le hu.1])
  · change |(-2 * w * (1 + q 0)) / (k * q 1)| ≤ 4 * w / k
    have hC0 : 0 ≤ 1 + q 0 := by linarith only [hC.1]
    have hratio : 2 * (1 + q 0) / q 1 ≤ 4 :=
      (div_le_iff₀ hd0).mpr (by linarith only [hC.2, hd])
    calc
      _ = (2 * (1 + q 0) / q 1) * (w / k) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hw.1, abs_of_nonneg hC0,
          abs_mul, abs_of_pos hk0, abs_of_pos hd0]
        norm_num
        ring
      _ ≤ 4 * (w / k) := mul_le_mul_of_nonneg_right hratio (div_nonneg hw.1 hk0.le)
      _ = _ := by ring
