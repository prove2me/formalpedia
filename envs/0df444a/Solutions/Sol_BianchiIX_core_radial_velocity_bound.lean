-- Prove2me | solution 1 for BianchiIX.core_radial_velocity_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:35:11.382966+00:00
-- url     : https://prove2.me/submissions/5911689d-aa9f-4ef3-909f-3b77ae227195

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_coupling_nonneg {k u v w : ℝ} (hk : 6 ≤ k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w) : 0 ≤ coupling u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  exact mul_nonneg hu.1 (by linarith)

end
end

private theorem BianchiIX.core_radial_numerator_bound {r u v w c : ℝ} (hr : 0 < r)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hC : 0 ≤ coupling u v w) (hc : |c| ≤ 1) :
    |-coupling u v w - c * (u - w) ^ 2 / r| ≤ u * v + u * w + u ^ 2 / r + w ^ 2 / r := by
  have hδ : (u - w) ^ 2 ≤ u ^ 2 + w ^ 2 := by nlinarith [mul_nonneg hu hw]
  have hprod : |c * (u - w) ^ 2 / r| ≤ (u - w) ^ 2 / r := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (u - w)), abs_of_pos hr]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (u - w)]) hr.le
  calc
    |-coupling u v w - c * (u - w) ^ 2 / r| ≤ coupling u v w + |c * (u - w) ^ 2 / r| := by
      simpa only [abs_neg, abs_of_nonneg hC] using abs_sub (-coupling u v w) (c * (u - w) ^ 2 / r)
    _ ≤ coupling u v w + (u ^ 2 + w ^ 2) / r := by
      have H := hprod.trans (div_le_div_of_nonneg_right hδ hr.le)
      linarith
    _ ≤ u * v + u * w + u ^ 2 / r + w ^ 2 / r := by
      rw [add_div]
      unfold coupling
      nlinarith [sq_nonneg u]

theorem solution {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hc : |c| ≤ 1) :
    |(-coupling u v w - c * (u - w) ^ 2 / r) / coreClockFactor r u w| ≤
      (u * v + u * w + u ^ 2 / r + w ^ 2 / r) / (999 / 1000) := by
  have hr0 : 0 < r := by linarith
  have hd := (coreBootstrap_clock_bounds hk hr hu hw).1
  have hd0 : 0 < coreClockFactor r u w := by linarith
  have hC := coreBootstrap_coupling_nonneg hk hv hu hw.1
  have hnum := core_radial_numerator_bound hr0 hu.1 hw.1 hC hc
  rw [abs_div, abs_of_pos hd0]
  exact (div_le_div_of_nonneg_right hnum hd0.le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans hnum) (by norm_num) hd)
