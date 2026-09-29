-- Prove2me | solution 1 for FamousTheorems.galois_group_symmetric_prime_degree_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:17:58.781324+00:00
-- url     : https://prove2.me/submissions/12409507-cad5-4b6e-bf87-9f804a800067

import Mathlib

theorem solution {p : Polynomial ℚ} (hirr : Irreducible p) (hdeg : p.natDegree.Prime)
    (hroots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (@Polynomial.Gal.galActionHom ℚ _ p ℂ _ _ Polynomial.Gal.splits_ℚ_ℂ) :=
  Polynomial.Gal.galActionHom_bijective_of_prime_degree hirr hdeg hroots
