-- Prove2me | solution 1 for FamousTheorems.weierstrass_uniform_limit_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:31:05.719322+00:00
-- url     : https://prove2.me/submissions/5eb4553f-1511-40d6-b78d-68dd805d7f40

import Mathlib

theorem solution {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U : Set ℂ} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → E} {f : ℂ → E} (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) : DifferentiableOn ℂ f U :=
  hf.differentiableOn hF hU
