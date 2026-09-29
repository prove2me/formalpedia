-- Prove2me | solution 1 for BookProof.YangMillsHermite.PolySym.comp_adj
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:12.309272+00:00
-- url     : https://prove2.me/submissions/01aa5ff4-bbac-46e5-aa92-e01d7ff34059

import Definitions.Def_ChapterHermiteProductCore
import Mathlib
set_option autoImplicit false
open BookProof.HermiteProductCore

theorem solution {d : ℕ} {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (S p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (S q)))
    (hT : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (T p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (T q))) :
    ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) ((S.comp T) p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * ((T.comp S) q)) := by
  intro p q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS, hT]

#print axioms solution
