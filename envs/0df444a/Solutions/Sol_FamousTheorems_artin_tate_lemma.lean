-- Prove2me | solution 1 for FamousTheorems.artin_tate_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:31:49.877162+00:00
-- url     : https://prove2.me/submissions/42f0a843-d24d-40d1-bfb7-622243c24b77

import Mathlib

theorem solution (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  fg_of_fg_of_fg A B C hAC hBC hBCi
