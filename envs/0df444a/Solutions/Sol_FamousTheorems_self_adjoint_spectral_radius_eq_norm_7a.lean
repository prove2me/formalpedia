-- Prove2me | solution 1 for FamousTheorems.self_adjoint_spectral_radius_eq_norm_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:38:01.370191+00:00
-- url     : https://prove2.me/submissions/9a4655d7-7bed-4186-a8bd-e76a592c2c85

import Mathlib

theorem solution {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) : spectralRadius ℂ a = (‖a‖₊ : ENNReal) :=
  ha.spectralRadius_eq_nnnorm
