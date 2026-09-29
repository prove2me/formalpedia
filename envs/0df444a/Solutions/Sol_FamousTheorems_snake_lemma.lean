-- Prove2me | solution 1 for FamousTheorems.snake_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:58:52.952468+00:00
-- url     : https://prove2.me/submissions/168e1438-753f-4d91-aef6-3f7f27caa8fb

import Mathlib

theorem solution {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C] (S : CategoryTheory.ShortComplex.SnakeInput C) :
    S.composableArrows.Exact :=
  S.snake_lemma
