-- Prove2me | solution 1 for BookProof.YangMillsHermite.PolyAdj.symm_of
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:11.620345+00:00
-- url     : https://prove2.me/submissions/ec3b279c-3cb5-4dba-84cc-aefa2479e1c2

import Definitions.Def_ChapterHermiteProductCore
import Mathlib
set_option autoImplicit false
open BookProof.HermiteProductCore

theorem solution {d : ℕ} {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (S p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (T q)))
    (h' : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (T p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (S q))) :
    ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) ((S + T) p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * ((S + T) q)) := by
  intro p q
  simp only [LinearMap.add_apply, map_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, h, h']
  ring

#print axioms solution
