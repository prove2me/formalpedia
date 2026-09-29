-- Prove2me | solution 1 for EulerMascheroni.gamma_irrational_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-10T07:03:22.25425+00:00
-- url     : https://prove2.me/submissions/4ab86454-5fa6-4f1a-8614-60242d2bcb58

import Mathlib

theorem solution
    (h : Transcendental ℚ Real.eulerMascheroniConstant) :
    Irrational Real.eulerMascheroniConstant :=
  h.irrational
