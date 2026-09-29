-- Prove2me | solution 1 for FamousTheorems.second_resolvent_identity_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:18:20.15992+00:00
-- url     : https://prove2.me/submissions/883b7b16-608c-462a-b838-83c22d04dd75

import Mathlib

theorem solution {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {a b : A} {r : R}
    (ha : r ∈ resolventSet R a) (hb : r ∈ resolventSet R b) :
    resolvent a r - resolvent b r = resolvent a r * (a - b) * resolvent b r :=
  spectrum.resolvent_sub_resolvent ha hb
