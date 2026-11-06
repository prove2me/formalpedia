-- Prove2me | solution 1 for BianchiIX.coreRegion_exit_radius_velocity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:57:40.137711+00:00
-- url     : https://prove2.me/submissions/2009a13e-d29c-4768-b02c-93402fa3530d

import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_core_radial_velocity_bound
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

private theorem BianchiIX.coreBootstrap_coupling_nonneg {k u v w : ℝ} (hk : 6 ≤ k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w) : 0 ≤ coupling u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  exact mul_nonneg hu.1 (by linarith)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

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

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

end
end

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

theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) :
    let f := coreAngleField (coreAngle (y 0) (y 2)) (toCoreAngleState y) 0
    f ≤ 0 ∧ |f| ≤ 2 * (y 1 + y 3 ^ 2 / coreRadius (y 0) (y 2)) := by
  intro f
  let r := coreRadius (y 0) (y 2)
  let z := coreAngle (y 0) (y 2)
  have hv : 0 < y 2 := by rw [hV]; norm_num
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hr0 : 0 < r := coreRadius_pos hv
  have hr1 : 1 ≤ r := by dsimp [r]; linarith only [hr.1, hk]
  have hd : 0 < coreClockFactor r (y 1) (y 3) := (coreRegion_clock_regular hk hy).2.1
  have hC := coreBootstrap_coupling_nonneg hk hy.2.1 hu hw.1
  have hz : 0 ≤ Real.tanh z := by
    rw [tanh_coreAngle hv]
    exact div_nonneg (sub_nonneg.mpr hM.le) hr0.le
  have hzabs : |Real.tanh z| ≤ 1 :=
    abs_le.mpr ⟨(Real.neg_one_lt_tanh z).le, (Real.tanh_lt_one z).le⟩
  have hid : f = (-coupling (y 1) (y 2) (y 3) - Real.tanh z * (y 1 - y 3) ^ 2 / r) /
      coreClockFactor r (y 1) (y 3) := coreAngleField_radius_projective hv
  constructor
  · rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_trans (neg_nonpos.mpr hC) (by positivity))) hd.le
  · have H := core_radial_velocity_bound hk hr.1 hy.2.1 hu hw hzabs
    change |(-coupling (y 1) (y 2) (y 3) - Real.tanh z * (y 1 - y 3) ^ 2 / r) /
      coreClockFactor r (y 1) (y 3)| ≤ _ at H
    rw [← hid] at H
    have hu' := coreBootstrap_wall_bound hk hu.2
    have hw' := coreBootstrap_wall_bound hk hw.2
    have huw : y 1 * y 3 ≤ y 1 / 60000 := by
      have H' := mul_le_mul_of_nonneg_left hw' hu.1
      linarith only [H']
    have huu : y 1 ^ 2 / r ≤ y 1 / 60000 := by
      have H' := mul_le_mul_of_nonneg_left hu' hu.1
      exact (div_le_self (sq_nonneg _) hr1).trans (by nlinarith only [H'])
    have hweak : 0 ≤ y 3 ^ 2 / r := div_nonneg (sq_nonneg _) hr0.le
    apply H.trans
    rw [show y 1 * y 2 = y 1 by rw [hV, mul_one]]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
    change y 1 + y 1 * y 3 + y 1 ^ 2 / r + y 3 ^ 2 / r ≤ _
    linarith only [huw, huu, hweak, hu.1]
