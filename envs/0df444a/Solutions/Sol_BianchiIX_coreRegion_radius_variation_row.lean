-- Prove2me | solution 1 for BianchiIX.coreRegion_radius_variation_row
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:36:27.936976+00:00
-- url     : https://prove2.me/submissions/d480accb-caf3-421f-866d-d1e26b798974

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRegion_amplitude_row_bounds
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

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
    |B.mulVec v 0| ≤
      (16 * y 1 + 8 / k ^ 2 * y 3 ^ 2 + 8 * (y 3 / (k * y 2))) * Q +
        2 * (|v 1| / Real.cosh (projectiveCoreAngle y)) + (1 / k) * |v 1| := by
  intro B
  have hk0 : 0 < k := by linarith only [hk]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hu0 := hy.2.2.1.1
  have hw0 := (coreRegion_wall_bounds hy).2.1
  have hQ0 : 0 ≤ Q := (norm_nonneg v).trans hQ
  have hc (i : Fin 3) : |v i| ≤ Q := (show |v i| ≤ ‖v‖ from norm_le_pi_norm v i).trans hQ
  obtain ⟨h00, h01, h02⟩ := coreRegion_amplitude_row_bounds hk hy
  change |B 0 1 + y 2 / k| ≤ 8 * (y 1 + y 3) / k at h01
  have hsmall : 8 * (y 1 + y 3) ≤ 1 := by
    have hu := coreBootstrap_wall_bound hk hy.2.2.1.2
    have hw := coreBootstrap_wall_bound hk (coreRegion_wall_bounds hy).2.2
    linarith only [hu, hw]
  have h01' : |B 0 1| ≤ y 2 / k + 1 / k := by
    have H := abs_add_le (B 0 1 + y 2 / k) (-(y 2 / k))
    rw [add_neg_cancel_right, abs_neg, abs_of_pos (div_pos hv hk0)] at H
    exact H.trans (by linarith only [h01, div_le_div_of_nonneg_right hsmall hk0.le])
  have h02' : |B 0 2| ≤ 8 * y 1 + 8 * (y 3 / (k * y 2)) := by
    have hu := div_le_self hu0 hy.2.1
    have hid : 8 * (y 1 + y 3 / k) / y 2 = 8 * (y 1 / y 2) + 8 * (y 3 / (k * y 2)) := by ring
    exact h02.trans (by rw [hid]; linarith only [hu])
  have hvk : y 2 / k ≤ 2 / Real.cosh (projectiveCoreAngle y) := by
    rw [← (coreAngle_coordinates (m := y 0) hv).1]
    have hr : coreRadius (y 0) (y 2) ≤ 2 * k := by
      linarith only [(coreRegion_radius_bounds hk hy).2, hk]
    calc
      coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)) / k =
          (coreRadius (y 0) (y 2) / k) / Real.cosh (projectiveCoreAngle y) := by
            dsimp [projectiveCoreAngle]
            ring
      _ ≤ 2 / Real.cosh (projectiveCoreAngle y) :=
        div_le_div_of_nonneg_right ((div_le_iff₀ hk0).mpr hr) (Real.cosh_pos _).le
  have hrow : B.mulVec v 0 = B 0 0 * v 0 + B 0 1 * v 1 + B 0 2 * v 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]
  rw [hrow]
  calc
    _ ≤ |B 0 0| * |v 0| + |B 0 1| * |v 1| + |B 0 2| * |v 2| := by
      have H := (abs_add_le (B 0 0 * v 0 + B 0 1 * v 1) (B 0 2 * v 2)).trans
        (add_le_add (abs_add_le (B 0 0 * v 0) (B 0 1 * v 1)) (le_refl _))
      simpa only [abs_mul] using H
    _ ≤ (8 * (y 1 + y 3 ^ 2 / k ^ 2)) * Q +
        (2 / Real.cosh (projectiveCoreAngle y) + 1 / k) * |v 1| +
        (8 * y 1 + 8 * (y 3 / (k * y 2))) * Q := by
      exact add_le_add (add_le_add
        (mul_le_mul h00 (hc 0) (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right (h01'.trans (add_le_add hvk (le_refl _))) (abs_nonneg _)))
        (mul_le_mul h02' (hc 2) (abs_nonneg _) (by positivity))
    _ = _ := by ring
