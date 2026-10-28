-- Prove2me | solution 1 for AvramDividend.Classical.mesh_exponential_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:20:14.929981+00:00
-- url     : https://prove2.me/submissions/3eb8e663-3252-4d6c-b541-48f5fae25188

import Mathlib

open Filter
theorem solution
    (r : ℕ → ℝ) (C : ℝ)
    (hr : Tendsto r atTop (nhds (0 : ℝ))) :
    Tendsto (fun n : ℕ => C * (1 - Real.exp (-(r n))))
      atTop (nhds (0 : ℝ)) := by
  have h : Tendsto (fun x : ℝ => C * (1 - Real.exp (-x))) (nhds 0) (nhds (C * (1 - Real.exp (-0)))) :=
    ((continuous_const.mul (continuous_const.sub (Real.continuous_exp.comp continuous_neg)))).tendsto 0
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero] at h
  exact h.comp hr
