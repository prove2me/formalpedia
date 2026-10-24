-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_antitone_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:51:58.517467+00:00
-- url     : https://prove2.me/submissions/025035ce-b216-41d2-a5fc-36ee333e9ff4

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (K : ℝ → ℝ) (β w : ℝ)
    (hw : 0 ≤ w)
    (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ K t) :
    AntitoneOn (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hm : -w * y ≤ -w * x := by
    have h := mul_nonneg hw (sub_nonneg.mpr hxy)
    nlinarith
  have he : Real.exp (-w * y) ≤ Real.exp (-w * x) :=
    Real.exp_le_exp.mpr hm
  have hK : K y ≤ K x := hanti hx hy hxy
  calc
    Real.exp (-w * y) * (|β| + K y) ≤
        Real.exp (-w * x) * (|β| + K y) :=
      mul_le_mul_of_nonneg_right he
        (add_nonneg (abs_nonneg β) (hKnonneg y hy))
    _ ≤ Real.exp (-w * x) * (|β| + K x) := by
      have hAdd : |β| + K y ≤ |β| + K x := by linarith [hK]
      exact mul_le_mul_of_nonneg_left hAdd (Real.exp_pos _).le
