-- Prove2me | solution 1 for FamousTheorems.spectrum_nonempty_banach_algebra_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:36:35.681829+00:00
-- url     : https://prove2.me/submissions/01a89a99-d654-47b2-8f1b-1ce626201071

import Mathlib

theorem solution {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a
