-- Prove2me | solution 1 for BookProof.YangMillsHermite.PolySym.add
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:10.028584+00:00
-- url     : https://prove2.me/submissions/be1fe91a-9300-41f1-a29d-dbb386147170

import Definitions.Def_ChapterHermiteProductCore
import Mathlib
set_option autoImplicit false
open BookProof.HermiteProductCore

theorem solution {d : ℕ} {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (S p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (S q)))
    (hT : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (T p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (T q))) :
    ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) ((S + T) p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * ((S + T) q)) := by
  intro p q
  simp only [LinearMap.add_apply, map_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, hS, hT]

#print axioms solution
