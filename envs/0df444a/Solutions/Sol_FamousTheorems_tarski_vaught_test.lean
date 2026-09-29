-- Prove2me | solution 1 for FamousTheorems.tarski_vaught_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:56:24.231222+00:00
-- url     : https://prove2.me/submissions/75510177-cd17-407e-8edb-ac2d5a456ebe

import Mathlib

theorem solution {L : FirstOrder.Language} {M N : Type*} [L.Structure M] [L.Structure N] (f : L.Embedding M N)
    (htv : ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) (a : N),
      φ.Realize default (Fin.snoc (f ∘ x) a : _ → N) →
        ∃ b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ → N)) :
    ∀ {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (f ∘ x) ↔ φ.Realize x :=
  f.isElementary_of_exists htv
