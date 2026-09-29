-- Prove2me | solution 1 for FamousTheorems.mellin_inversion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:19:39.639898+00:00
-- url     : https://prove2.me/submissions/d154c1ee-4b38-4bf8-8843-dac034dad11f

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (σ : ℝ) (f : ℝ → E) {x : ℝ}
    (hx : 0 < x) (hf : MellinConvergent f (σ : ℂ))
    (hFf : Complex.VerticalIntegrable (mellin f) σ MeasureTheory.volume) (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x :=
  mellinInv_mellin_eq σ f hx hf hFf hfx
