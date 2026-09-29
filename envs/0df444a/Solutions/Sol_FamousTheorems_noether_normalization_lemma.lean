-- Prove2me | solution 1 for FamousTheorems.noether_normalization_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:56:25.314201+00:00
-- url     : https://prove2.me/submissions/26cde962-49bd-49df-92d0-b1d96d27a491

import Mathlib

theorem solution (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R] [Algebra.FiniteType k R] :
    ∃ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] R), Function.Injective g ∧ g.IsIntegral :=
  exists_integral_inj_algHom_of_fg k R
