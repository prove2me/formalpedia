-- Prove2me | solution 1 for AvramDividend.Classical.esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:47:20.821575+00:00
-- url     : https://prove2.me/submissions/97bee5dd-e686-4558-a44e-bcdb44545c3b

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution (φ : ℝ) (W V : ℝ → ℝ)
    (hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  have hconst : ContDiff ℝ 1 (fun _ : ℝ => (φ : ℝ)) :=
    contDiff_const (𝕜 := ℝ) (E := ℝ) (F := ℝ) (c := φ)
  have hid : ContDiff ℝ 1 (fun x : ℝ => x) := contDiff_id
  have hlin : ContDiff ℝ 1 (fun x : ℝ => φ * x) := by
    simpa only [Pi.one_apply, one_mul] using
      (ContDiff.mul (f := fun _ : ℝ => (φ : ℝ))
        (g := fun x : ℝ => x) hconst hid)
  have hexp : ContDiff ℝ 1 (fun x : ℝ => Real.exp (φ * x)) := by
    have he : ContDiff ℝ 1 (Real.exp : ℝ → ℝ) := Real.contDiff_exp
    simpa only [Function.comp_def] using (ContDiff.comp he hlin)
  have hprod : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (φ * x) * V x) (Ioi (0 : ℝ)) :=
    ContDiffOn.mul hexp.contDiffOn hVdiff
  have hpoint : ∀ x : ℝ, 0 < x → Real.exp (φ * x) * V x = W x := by
    intro x hx
    rw [hV x hx, ← mul_assoc, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, one_mul]
  exact hprod.congr (fun x hx => (hpoint x hx).symm)
