-- Prove2me | solution 1 for BookProof.YangMillsHermite.PolySym.real_smul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:10.751704+00:00
-- url     : https://prove2.me/submissions/fa371c57-6e10-4f79-aa58-2576f7ba8f46

import Definitions.Def_ChapterHermiteProductCore
import Mathlib
set_option autoImplicit false
open BookProof.HermiteProductCore

theorem solution {d : ℕ} {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (T p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (T q))) :
    ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (MvPolynomial.map (starRingEnd ℂ) (((t : ℂ) • T) p) * (q)) = gaussInt (MvPolynomial.map (starRingEnd ℂ) (p) * (((t : ℂ) • T) q)) := by
  have hstar (r : MvPolynomial (Fin d) ℂ) :
      MvPolynomial.map (starRingEnd ℂ) ((t : ℂ) • r) =
        (t : ℂ) • MvPolynomial.map (starRingEnd ℂ) r := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
      Complex.conj_ofReal]
  intro p q
  simp only [LinearMap.smul_apply, hstar, smul_mul_assoc, mul_smul_comm]
  rw [gaussInt_smul, gaussInt_smul, hT]

#print axioms solution
