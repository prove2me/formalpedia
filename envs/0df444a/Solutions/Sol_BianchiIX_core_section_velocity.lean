-- Prove2me | solution 1 for BianchiIX.core_section_velocity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:02:08.593261+00:00
-- url     : https://prove2.me/submissions/d7886e06-e7a7-4ae4-a93b-68f5bdcc7092

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination

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

private theorem BianchiIX.core_section_phase_gap {k m : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1) : 3 * k / 4 ≤ |m - 1| := by
  have hr2 := (sq_le_sq₀ (by linarith : 0 ≤ 99 / 100 * k)
    (show 0 ≤ coreRadius m 1 from Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  apply (sq_le_sq₀ (by linarith : 0 ≤ 3 * k / 4) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (k - 6)]

private theorem BianchiIX.core_section_coupling_bound {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    0 ≤ coupling u 1 w ∧ coupling u 1 w ≤ 1 / 1000 := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  refine ⟨coreBootstrap_coupling_nonneg hk le_rfl hu hw.1, ?_⟩
  have H := mul_le_mul hu' (show 1 + w - u ≤ 2 by linarith)
    (show 0 ≤ 1 + w - u by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 60000)
  exact H.trans (by norm_num)

/-- The activity equation alone determines the orientation of both core crossings. -/
theorem solution {k m u w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (1 < m ∧ k / 2 ≤ activeVelocity m u 1 w) ∨
      (m < 1 ∧ activeVelocity m u 1 w ≤ -k / 2) := by
  have hgap := core_section_phase_gap hk hr
  have hC := core_section_coupling_bound hk hu hw
  by_cases hm : 1 ≤ m
  · rw [abs_of_nonneg (sub_nonneg.mpr hm)] at hgap
    left
    unfold activeVelocity
    constructor <;> nlinarith
  · rw [abs_of_neg (by linarith : m - 1 < 0)] at hgap
    right
    unfold activeVelocity
    constructor <;> nlinarith
