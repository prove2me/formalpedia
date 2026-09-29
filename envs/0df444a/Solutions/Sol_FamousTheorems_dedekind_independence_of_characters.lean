-- Prove2me | solution 1 for FamousTheorems.dedekind_independence_of_characters
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:02:45.657155+00:00
-- url     : https://prove2.me/submissions/3b9dc4b3-a083-40cf-a73b-6cbc0a4d300c

import Mathlib

theorem solution (G L : Type*) [MulOneClass G] [CommRing L] [IsDomain L] :
    LinearIndependent L (fun f : G →* L => (f : G → L)) :=
  linearIndependent_monoidHom G L
