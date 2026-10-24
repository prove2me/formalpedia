-- Prove2me | solution 1 for AvramDividend.Classical.esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:16:49.792813+00:00
-- url     : https://prove2.me/submissions/76cbbc1e-3b7c-4125-8f3a-37cf531eb3cf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (φ : ℝ) (W V : ℝ → ℝ)
    (hVc : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) := by
  have hExp : ContDiffOn ℝ 2 (fun x : ℝ => Real.exp (φ * x))
      (Ioi (0 : ℝ)) := by
    fun_prop
  have hprod : ContDiffOn ℝ 2
      (fun x : ℝ => Real.exp (φ * x) * V x)
      (Ioi (0 : ℝ)) := hExp.mul hVc
  apply hprod.congr
  intro x hx
  have he : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    W x = 1 * W x := (one_mul _).symm
    _ = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by rw [he]
    _ = Real.exp (φ * x) * V x := by rw [hV x hx]; ring
