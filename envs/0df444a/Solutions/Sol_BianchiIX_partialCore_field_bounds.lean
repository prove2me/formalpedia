-- Prove2me | solution 1 for BianchiIX.partialCore_field_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:06:56.832192+00:00
-- url     : https://prove2.me/submissions/a8f6f759-a2d0-4265-bfbe-60b20170f953

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreRegion_log_rate_bounds
import Theorems.Thm_BianchiIX_core_radial_velocity_bound
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
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

private theorem BianchiIX.coreAngleField_auxiliary (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y = ![(coreAuxiliary z y) 3 / (coreAuxiliary z y) 1,
      y 1 * (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1,
      -2 * y 2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1)] := rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngleField_log_rates (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y 1 = y 1 * coreLogRates z y 0 ∧
      coreAngleField z y 2 = y 2 * coreLogRates z y 1 := by
  rw [coreAngleField_auxiliary]
  constructor <;> dsimp [coreLogRates] <;> ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

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

/-- The angular field at an arbitrary interior entrance retains both small wall amplitudes. -/
theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k) :
    let F := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)
    let p := y 2 * y 3
    |F 0| ≤ 2 * (k * y 1 + p ^ 2 / k) ∧
      |F 1| ≤ 2 * k * y 1 ∧ |F 2| ≤ 4 * p / k := by
  intro F p
  have hk0 : 0 < k := by linarith only [hk]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hp : 0 ≤ p := hy.2.2.2.1
  have hvk : y 2 ≤ k := by
    simpa only [hR, abs_of_pos hv] using (coreRadius_component_bounds (y 0) (y 2)).2
  have hwp : y 3 ≤ p := by
    dsimp [p]
    nlinarith only [mul_le_mul_of_nonneg_right hy.2.1 hw.1]
  have hw2 : y 3 ^ 2 / k ≤ p ^ 2 / k :=
    div_le_div_of_nonneg_right ((sq_le_sq₀ hw.1 hp).mpr hwp) hk0.le
  have huv : y 1 * y 2 ≤ k * y 1 := by
    nlinarith only [mul_le_mul_of_nonneg_left hvk hu.1]
  have huw : y 1 * y 3 ≤ y 1 / 60000 := by
    nlinarith only [mul_le_mul_of_nonneg_left (coreBootstrap_wall_bound hk hw.2) hu.1]
  have huu : y 1 ^ 2 / k ≤ y 1 / 60000 :=
    (div_le_self (sq_nonneg _) (by linarith only [hk])).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left (coreBootstrap_wall_bound hk hu.2) hu.1])
  obtain ⟨hU, hP, _⟩ := coreRegion_log_rate_bounds hk hy
  have hcoef := coreAngleField_log_rates (projectiveCoreAngle y) (toCoreAngleState y)
  refine ⟨?_, ?_, ?_⟩
  · have H := core_radial_velocity_bound hk
      (r := k) (by linarith only [hk]) hy.2.1 hu hw
      (Real.abs_tanh_lt_one (projectiveCoreAngle y)).le
    have hid := coreAngleField_radius_projective hv
    rw [hR] at hid
    change F 0 = _ at hid
    rw [hid]
    apply H.trans
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
    have hku : 6 * y 1 ≤ k * y 1 := mul_le_mul_of_nonneg_right hk hu.1
    have hp2 : 0 ≤ p ^ 2 / k := div_nonneg (sq_nonneg _) hk0.le
    linarith only [huv, huw, huu, hw2, hku, hu.1, hp2]
  · change |coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 1| ≤ _
    rw [hcoef.1, abs_mul]
    change |y 1| * _ ≤ _
    rw [abs_of_nonneg hu.1]
    have H := mul_le_mul_of_nonneg_right hU hu.1
    convert! H using 1
    ring
  · change |coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 2| ≤ _
    rw [hcoef.2, abs_mul]
    change |p| * _ ≤ _
    rw [abs_of_nonneg hp]
    have H := mul_le_mul_of_nonneg_right hP hp
    convert! H using 1 <;> ring
