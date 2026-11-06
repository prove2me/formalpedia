-- Prove2me | solution 1 for BianchiIX.coreRegion_exit_angle_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:01:08.103261+00:00
-- url     : https://prove2.me/submissions/605325aa-852b-45c8-aa28-fb3cd17aa84b

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRegion_exit_radius_velocity
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
open Set Filter
open scoped Topology

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

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_section_phase_gap {k m : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1) : 3 * k / 4 ≤ |m - 1| := by
  have hr2 := (sq_le_sq₀ (by linarith : 0 ≤ 99 / 100 * k)
    (show 0 ≤ coreRadius m 1 from Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  apply (sq_le_sq₀ (by linarith : 0 ≤ 3 * k / 4) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (k - 6)]

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

theorem solution {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) (q : ℝ) :
    |(-q) / (coreRadius (y 0) (y 2) * (-Real.tanh (projectiveCoreAngle y) +
      coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2)))| ≤
      2 * |q| / k := by
  let r := coreRadius (y 0) (y 2)
  let f := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0
  have hv : 0 < y 2 := by rw [hV]; norm_num
  have hr : 0 < r := coreRadius_pos hv
  have hrange := coreRegion_radius_bounds hk hy
  have hgap := core_section_phase_gap hk
    (show 99 / 100 * k ≤ coreRadius (y 0) 1 by simpa only [hV] using hrange.1)
  rw [abs_of_neg (sub_neg.mpr hM)] at hgap
  have hf : f ≤ 0 := (coreRegion_exit_radius_velocity hk hy hV hM).1
  have hden : r * (-Real.tanh (projectiveCoreAngle y) + f / r) = y 0 - 1 + f := by
    rw [projectiveCoreAngle, tanh_coreAngle hv]
    change r * (-((1 - y 0) / r) + f / r) = _
    field_simp
    ring
  have hk0 : 0 < k := by linarith only [hk]
  have hnegative : y 0 - 1 + f < 0 := by linarith only [hM, hf]
  have hlower : k / 2 ≤ -(y 0 - 1 + f) := by linarith only [hgap, hf, hk]
  change |(-q) / (r * (-Real.tanh (projectiveCoreAngle y) + f / r))| ≤ _
  rw [hden, abs_div, abs_neg, abs_of_neg hnegative]
  calc
    |q| / -(y 0 - 1 + f) ≤ |q| / (k / 2) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hlower
    _ = 2 * |q| / k := by ring
