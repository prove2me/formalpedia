-- Prove2me | solution 1 for BianchiIX.coreRegion_original_log_rate_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:58:09.734726+00:00
-- url     : https://prove2.me/submissions/6cf4def5-77db-48fd-8985-4cc5919938e9

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreBootstrap_strong_numerator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set MeasureTheory

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

private theorem BianchiIX.coreBootstrap_strong_rate {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : v ≤ r) (hc : -1 ≤ c)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (-r / 2 - c + (v / r) * w + (u ^ 2 - w ^ 2) / (2 * r)) / coreClockFactor r u w ≤ -k / 4 := by
  have ha := coreBootstrap_strong_numerator hk hr hv hc hu hw
  obtain ⟨hdlo, hdhi⟩ := coreBootstrap_clock_bounds hk hr hu hw
  apply (div_le_iff₀ (show 0 < coreClockFactor r u w by linarith)).mpr
  nlinarith

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreAuxiliary_projective_clockFactor {y : ProjectiveState} (hv : 0 < y 2) :
    coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 =
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

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

private theorem BianchiIX.coreLogRates_strong_decay {k z : ℝ} {Y : CoreAngleState} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ Y 2 / (Y 0 / Real.cosh z) ∧ Y 2 / (Y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    coreLogRates z Y 0 ≤ -k / 4 := by
  have hr0 : 0 < Y 0 := by linarith only [hk, hr]
  have hv : Y 0 / Real.cosh z ≤ Y 0 :=
    (div_le_iff₀ (Real.cosh_pos z)).mpr (le_mul_of_one_le_right hr0.le (Real.one_le_cosh z))
  have H := coreBootstrap_strong_rate hk hr hv
    (show -1 ≤ -Real.tanh z by linarith [Real.tanh_lt_one z]) hu hw
  convert! H using 1
  dsimp [coreLogRates, coreAuxiliary]
  congr 1
  field_simp
  ring

/-- Original-time rates remain strictly negative even when either wall amplitude vanishes. -/
theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    coreOriginalLogRates y 0 ≤ (-k ^ 2 / 10) * (6 / projectiveStateDenom y) ∧
      coreOriginalLogRates y 1 ≤ -2 * (6 / projectiveStateDenom y) := by
  let r := coreRadius (y 0) (y 2)
  let d := coreClockFactor r (y 1) (y 3)
  let a := 6 / projectiveStateDenom y
  have hk0 : 0 < k := by linarith only [hk]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hr := (coreRegion_radius_bounds hk hy).1
  have hr0 : 0 < r := coreRadius_pos hv
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hd := coreBootstrap_clock_bounds hk hr hu hw
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000) hd.1
  have ha : 0 ≤ a := (div_pos (by norm_num) (coreRegion_clock_regular hk hy).1).le
  have hW : (toCoreAngleState y) 2 / ((toCoreAngleState y) 0 / Real.cosh (projectiveCoreAngle y)) = y 3 := by
    change y 2 * y 3 / (r / Real.cosh (coreAngle (y 0) (y 2))) = _
    rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]
  have hstrong := coreLogRates_strong_decay (Y := toCoreAngleState y) (z := projectiveCoreAngle y)
    hk hr hu (by simpa only [hW] using hw)
  have hrd : k / 2 ≤ r * d := by
    have H := mul_le_mul hr hd.1 (by norm_num : (0 : ℝ) ≤ 999 / 1000) hr0.le
    nlinarith only [H, hk]
  have hrq : 0 ≤ r * d := mul_nonneg hr0.le hd0.le
  have hC := coreBootstrap_coupling_nonneg hk hy.2.1 hu hw.1
  constructor
  · have H := mul_le_mul_of_nonneg_left hstrong hrq
    have H' := mul_le_mul_of_nonpos_right hrd (show -k / 4 ≤ 0 by linarith only [hk])
    have hcoef : r * d * coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) 0 ≤ -k ^ 2 / 10 := by
      nlinarith only [H, H', sq_nonneg k]
    have H'' := mul_le_mul_of_nonneg_left hcoef ha
    convert! H'' using 1 <;> dsimp [coreOriginalLogRates, coreOriginalClockRate, a, r, d] <;> ring
  · have hid : r * d * coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) 1 =
        -2 * (1 + coupling (y 1) (y 2) (y 3)) := by
      change r * d * (-2 * (1 + coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 0) /
        (r * coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1)) = _
      rw [coreAuxiliary_projective_clockFactor hv]
      have hq : coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 0 =
          coupling (y 1) (y 2) (y 3) := by
        change coupling (y 1) (r / Real.cosh (coreAngle (y 0) (y 2)))
          (y 2 * y 3 / (r / Real.cosh (coreAngle (y 0) (y 2)))) = _
        rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]
      rw [hq]
      change r * d * (-2 * (1 + coupling (y 1) (y 2) (y 3)) / (r * d)) = _
      field_simp
    have H := mul_le_mul_of_nonneg_left (show r * d *
        coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) 1 ≤ -2 by rw [hid]; linarith only [hC]) ha
    convert! H using 1 <;> dsimp [coreOriginalLogRates, coreOriginalClockRate, a, r, d] <;> ring
