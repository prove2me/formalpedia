-- Prove2me | solution 1 for BianchiIX.coreBootstrap_phase_velocity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:02:51.777203+00:00
-- url     : https://prove2.me/submissions/7d34d981-6856-4bf7-9d6b-160bed21bf5e

import Definitions.Def_BianchiIX_Algebra_Projective
import Theorems.Thm_BianchiIX_phaseVelocity_factor
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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

/-- The factored phase equation gives two-sided speed bounds throughout the core. -/
theorem solution {k m u v w : ℝ} (hk : 6 ≤ k)
    (hm : |m| ≤ 6 / 5 * k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    v ^ 2 / 2 ≤ -phaseVelocity m u v w ∧ -phaseVelocity m u v w ≤ 2 * v ^ 2 := by
  have hk0 : 0 < k := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hmu : |m * u| ≤ 1 / 1000 := by
    rw [abs_mul, abs_of_nonneg hu.1]
    calc
      |m| * u ≤ (6 / 5 * k) * ((1 / 10000) / k) :=
        mul_le_mul hm hu.2 hu.1 (by positivity)
      _ ≤ 1 / 1000 := by field_simp; norm_num
  have hmul := abs_le.mp hmu
  have h₁ : 9 / 10 * v ≤ v + w - u ∧ v + w - u ≤ 11 / 10 * v := by
    constructor <;> linarith
  have h₂ : 9 / 10 * v ≤ v - w + m * u ∧ v - w + m * u ≤ 11 / 10 * v := by
    constructor <;> linarith
  have hlo := mul_le_mul h₁.1 h₂.1 (by linarith : 0 ≤ 9 / 10 * v)
    (by linarith : 0 ≤ v + w - u)
  have hhi := mul_le_mul h₁.2 h₂.2 (by linarith : 0 ≤ v - w + m * u)
    (by linarith : 0 ≤ 11 / 10 * v)
  rw [phaseVelocity_factor]
  constructor <;> nlinarith [sq_nonneg v]
