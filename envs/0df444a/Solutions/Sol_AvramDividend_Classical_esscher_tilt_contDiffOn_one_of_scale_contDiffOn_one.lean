-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:43:04.260983+00:00
-- url     : https://prove2.me/submissions/8d3ad346-5716-452a-a5cd-65a9f8dbfbaa

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution (φ : ℝ) (W V : ℝ → ℝ)
    (hW : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  have hconst : ContDiff ℝ 1 (fun _ : ℝ => (φ : ℝ)) :=
    contDiff_const (𝕜 := ℝ) (E := ℝ) (F := ℝ) (c := φ)
  have hid : ContDiff ℝ 1 (fun x : ℝ => x) := contDiff_id
  have hlin : ContDiff ℝ 1 (fun x : ℝ => φ * x) := by
    simpa only [Pi.one_apply, one_mul] using
      (ContDiff.mul (f := fun _ : ℝ => (φ : ℝ))
        (g := fun x : ℝ => x) hconst hid)
  have hneg : ContDiff ℝ 1 (fun x : ℝ => -(φ * x)) := hlin.neg
  have hexp : ContDiff ℝ 1 (fun x : ℝ => Real.exp (-(φ * x))) := by
    have he : ContDiff ℝ 1 (Real.exp : ℝ → ℝ) := Real.contDiff_exp
    simpa only [Function.comp_def] using (ContDiff.comp he hneg)
  have hprod : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) :=
    ContDiffOn.mul hexp.contDiffOn hW
  exact hprod.congr (fun x hx => hV x hx)
