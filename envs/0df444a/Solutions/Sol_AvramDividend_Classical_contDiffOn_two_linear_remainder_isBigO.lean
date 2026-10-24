-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_two_linear_remainder_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:48:51.32489+00:00
-- url     : https://prove2.me/submissions/141be4b9-23d1-40b8-86c7-e2b9f06308d8

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

/-- Quadratic control of the first-order remainder of a C2 real function. -/
theorem solution
    (f : ℝ → ℝ) (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    (fun y : ℝ => f (x + y) - f x - deriv f x * y) =O[𝓝 0]
      (fun y : ℝ => y ^ 2) := by
  have hsnhds : Ioo (0 : ℝ) a ∈ 𝓝 x :=
    isOpen_Ioo.mem_nhds hx
  have hfilter : 𝓝[Ioo (0 : ℝ) a] x = 𝓝 x :=
    nhdsWithin_eq_nhds.mpr hsnhds
  have htaylor :=
    taylor_isLittleO (convex_Ioo (0 : ℝ) a) hx hf
  rw [hfilter] at htaylor
  have hshift : Tendsto (fun y : ℝ => x + y) (𝓝 0) (𝓝 x) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun y : ℝ => x + y) (𝓝 0) (𝓝 (x + 0)))
  have hrem :
      (fun y : ℝ =>
        f (x + y) -
          taylorWithinEval f 2 (Ioo (0 : ℝ) a) x (x + y))
        =o[𝓝 0] (fun y : ℝ => y ^ 2) := by
    simpa [Function.comp_def] using htaylor.comp_tendsto hshift
  have hderiv :
      derivWithin f (Ioo (0 : ℝ) a) x = deriv f x :=
    derivWithin_of_isOpen isOpen_Ioo hx
  have htaylor_eval (y : ℝ) :
      taylorWithinEval f 2 (Ioo (0 : ℝ) a) x (x + y) =
        f x + deriv f x * y +
          ((2 : ℝ)⁻¹ * iteratedDerivWithin 2 f (Ioo (0 : ℝ) a) x) * y ^ 2 := by
    rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ]
    rw [taylorWithinEval_succ, taylor_within_zero_eval]
    rw [iteratedDerivWithin_one, hderiv]
    simp [smul_eq_mul]
    ring
  let c : ℝ :=
    (2 : ℝ)⁻¹ * iteratedDerivWithin 2 f (Ioo (0 : ℝ) a) x
  have hquad :
      (fun y : ℝ => c * y ^ 2) =O[𝓝 0] (fun y : ℝ => y ^ 2) :=
    isBigO_const_mul_self c (fun y : ℝ => y ^ 2) (𝓝 0)
  have hsum :
      (fun y : ℝ =>
        (f (x + y) -
          taylorWithinEval f 2 (Ioo (0 : ℝ) a) x (x + y)) +
        c * y ^ 2) =O[𝓝 0] (fun y : ℝ => y ^ 2) :=
    hrem.isBigO.add hquad
  apply hsum.congr_left
  intro y
  rw [htaylor_eval]
  dsimp [c]
  ring
