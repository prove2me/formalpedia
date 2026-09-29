-- Prove2me | solution 1 for FamousTheorems.isaacs_alg_closure_criterion_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:09:40.734971+00:00
-- url     : https://prove2.me/submissions/e42b7e77-c6d0-4790-b4a1-0f69a144593c

import Mathlib

theorem solution {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (h : ∀ p : Polynomial F, p.Monic → Irreducible p → ∃ x : E, Polynomial.aeval x p = 0) : IsAlgClosure F E :=
  IsAlgClosure.of_exists_root h
