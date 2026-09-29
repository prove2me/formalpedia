-- Prove2me | solution 1 for FamousTheorems.hahn_embedding_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:24:37.418511+00:00
-- url     : https://prove2.me/submissions/882d555a-409d-46f0-9a47-d3923142034b

import Mathlib

theorem solution (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] :
    ∃ f : M →+o Lex (HahnSeries (FiniteArchimedeanClass M) ℝ), Function.Injective f ∧
      ∀ a : M, ArchimedeanClass.mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop :=
  hahnEmbedding_isOrderedAddMonoid M
