-- Prove2me | solution 1 for BianchiIX.coreRegion_strong_forcing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:58:46.803849+00:00
-- url     : https://prove2.me/submissions/5c9fafac-3c68-4f74-bfa6-b9440427a968

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreWeightedJacobian_strong_bound
import Theorems.Thm_BianchiIX_coreWeightedJacobian_strong_off_diagonal
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
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

theorem solution {k Q : ℝ} {y : ProjectiveState} {v : CoreAngleState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hQ : ‖v‖ ≤ Q) :
    let B := coreWeightedJacobian k (projectiveCoreAngle y) (toCoreAngleState y)
    B 1 1 ≤ -k / 4 ∧ |B 1 0 * v 0 + B 1 2 * v 2| ≤ 3 * k * y 1 * Q := by
  intro B
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hcoord := (coreAngle_coordinates (m := y 0) hv).1
  have hV : 1 ≤ toCoreAngleState y 0 / Real.cosh (projectiveCoreAngle y) := by
    change 1 ≤ coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))
    rw [hcoord]
    exact hy.2.1
  have hW : 0 ≤ toCoreAngleState y 2 / (toCoreAngleState y 0 / Real.cosh (projectiveCoreAngle y)) ∧
      toCoreAngleState y 2 / (toCoreAngleState y 0 / Real.cosh (projectiveCoreAngle y)) ≤ (1 / 10000) / k := by
    change 0 ≤ y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ∧
      y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ≤ _
    rw [hcoord, mul_div_cancel_left₀ _ (ne_of_gt hv)]
    exact (coreRegion_wall_bounds hy).2
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨h10, h12⟩ := coreWeightedJacobian_strong_off_diagonal hk hr hV hy.2.2.1 hW
  refine ⟨coreWeightedJacobian_strong_bound hk hr.1 hy.2.2.1 hW, ?_⟩
  have hQ0 : 0 ≤ Q := (norm_nonneg v).trans hQ
  have hc (i : Fin 3) : |v i| ≤ Q := (show |v i| ≤ ‖v‖ by exact norm_le_pi_norm v i).trans hQ
  calc
    _ ≤ |B 1 0| * |v 0| + |B 1 2| * |v 2| := by simpa only [abs_mul] using abs_add_le (B 1 0 * v 0) (B 1 2 * v 2)
    _ ≤ (2 * k * y 1) * Q + (4 * y 1) * Q := add_le_add
      (mul_le_mul h10 (hc 0) (abs_nonneg _) (by have := hy.2.2.1.1; positivity))
      (mul_le_mul h12 (hc 2) (abs_nonneg _) (by have := hy.2.2.1.1; positivity))
    _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ k - 4 by linarith only [hk]) (mul_nonneg hy.2.2.1.1 hQ0)]
