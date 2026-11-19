-- Prove2me | solution 1 for DerandLDT.observation_3_14
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:14:14.218221+00:00
-- url     : https://prove2.me/submissions/e63c5110-2069-4aaf-a212-edc150e70182

import Mathlib

universe u

open Polynomial

theorem solution (F : Type u) [Field F] (f g : Polynomial (MvPolynomial (Fin 2) F))
    (hf : 1 ≤ f.natDegree) (hg : 1 ≤ g.natDegree) (a : Fin 2 → F)
    (hfa : (f.map (MvPolynomial.eval a)).natDegree = f.natDegree)
    (hga : (g.map (MvPolynomial.eval a)).natDegree = g.natDegree) :
    MvPolynomial.eval a (resultant f g) =
      resultant (f.map (MvPolynomial.eval a)) (g.map (MvPolynomial.eval a)) := by
  rw [hfa, hga, resultant_map_map]
