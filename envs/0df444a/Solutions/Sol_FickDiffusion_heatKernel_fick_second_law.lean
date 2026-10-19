-- Prove2me | solution 1 for FickDiffusion.heatKernel_fick_second_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:04:59.14074+00:00
-- url     : https://prove2.me/submissions/bf91b5ae-c8b1-413f-8bd3-710eba74bb73

import Mathlib
import Definitions.Def_FickDiffusion_defs
open Real Filter Topology MeasureTheory FickDiffusion

theorem solution (D : ℝ) (hD : 0 < D) (x t : ℝ) (ht : 0 < t) :
    deriv (fun s => heatKernel D x s) t =
      D * deriv (fun y => deriv (fun z => heatKernel D z t) y) x := by
  have hc : 0 < 4 * D * t := by positivity
  have hq : 0 < 4 * π * D * t := by positivity
  set A := 1 / Real.sqrt (4 * π * D * t) with hA
  -- first space derivative
  have hd1 : ∀ y : ℝ, HasDerivAt (fun z => heatKernel D z t)
      (A * (Real.exp (-y ^ 2 / (4 * D * t)) * (-(2 * y) / (4 * D * t)))) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / (4 * D * t)) (-(2 * y) / (4 * D * t)) y := by
      have := ((hasDerivAt_pow 2 y).neg).div_const (4 * D * t)
      exact this.congr_deriv (by norm_num <;> ring)
    exact (h1.exp).const_mul A
  have hderiv1 : deriv (fun z => heatKernel D z t) =
      fun y => A * (Real.exp (-y ^ 2 / (4 * D * t)) * (-(2 * y) / (4 * D * t))) :=
    funext fun y => (hd1 y).deriv
  -- second space derivative
  have hd2 : HasDerivAt (fun y => A * (Real.exp (-y ^ 2 / (4 * D * t)) * (-(2 * y) / (4 * D * t))))
      (A * (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t)) * (-(2 * x) / (4 * D * t))
        + Real.exp (-x ^ 2 / (4 * D * t)) * (-2 / (4 * D * t)))) x := by
    have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / (4 * D * t)) (-(2 * x) / (4 * D * t)) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const (4 * D * t)
      exact this.congr_deriv (by norm_num <;> ring)
    have h2 : HasDerivAt (fun z : ℝ => -(2 * z) / (4 * D * t)) (-2 / (4 * D * t)) x := by
      have := (((hasDerivAt_id' x).const_mul 2).neg).div_const (4 * D * t)
      exact this.congr_deriv (by norm_num <;> ring)
    exact ((h1.exp).mul h2).const_mul A
  rw [hderiv1, hd2.deriv]
  -- time derivative
  have ht1 : HasDerivAt (fun s => Real.sqrt (4 * π * D * s))
      (4 * π * D / (2 * Real.sqrt (4 * π * D * t))) t := by
    have := ((hasDerivAt_id' t).const_mul (4 * π * D)).sqrt (by positivity)
    exact this.congr_deriv (by norm_num <;> ring)
  have ht2 : HasDerivAt (fun s => 1 / Real.sqrt (4 * π * D * s))
      (-(4 * π * D / (2 * Real.sqrt (4 * π * D * t))) / Real.sqrt (4 * π * D * t) ^ 2) t := by
    have := (hasDerivAt_const t (1 : ℝ)).div ht1 (Real.sqrt_pos.mpr hq).ne'
    exact this.congr_deriv (by norm_num <;> ring)
  have ht3 : HasDerivAt (fun s => -x ^ 2 / (4 * D * s)) (x ^ 2 * (4 * D) / (4 * D * t) ^ 2) t := by
    have := (hasDerivAt_const t (-x ^ 2)).div ((hasDerivAt_id' t).const_mul (4 * D)) (by positivity)
    exact this.congr_deriv (by norm_num <;> ring)
  have ht4 : HasDerivAt (fun s => 1 / Real.sqrt (4 * π * D * s) * Real.exp (-x ^ 2 / (4 * D * s)))
      (-(4 * π * D / (2 * Real.sqrt (4 * π * D * t))) / Real.sqrt (4 * π * D * t) ^ 2 *
        Real.exp (-x ^ 2 / (4 * D * t)) + 1 / Real.sqrt (4 * π * D * t) *
        (Real.exp (-x ^ 2 / (4 * D * t)) * (x ^ 2 * (4 * D) / (4 * D * t) ^ 2))) t :=
    ht2.mul (ht3.exp)
  have hfun : (fun s => heatKernel D x s) =
      fun s => 1 / Real.sqrt (4 * π * D * s) * Real.exp (-x ^ 2 / (4 * D * s)) := rfl
  rw [hfun, ht4.deriv]
  have hs : Real.sqrt (4 * π * D * t) ^ 2 = 4 * π * D * t := Real.sq_sqrt hq.le
  have hs0 : Real.sqrt (4 * π * D * t) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  rw [hA, hs]
  field_simp
  ring
