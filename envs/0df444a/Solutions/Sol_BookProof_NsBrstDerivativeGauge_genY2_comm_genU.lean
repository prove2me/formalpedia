-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.genY2_comm_genU
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T03:41:37.466997+00:00
-- url     : https://prove2.me/submissions/560c9efd-0e36-456e-8e1b-049111b49a3b

import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY2

open MvPolynomial BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2 BookProof.NsBrstDerivativeGauge in
theorem solution (i j : Fin 3) : genY2 j * genU i = genU i * genY2 j := by
  refine LinearMap.ext fun p => ?_
  have hm : ∀ (v : NSVar), v ≠ NSVar.u i → ∀ q : NSAlg,
      pderiv (NSVar.u i) (X v * q) = X v * pderiv (NSVar.u i) q := by
    intro v hv q
    rw [Derivation.leibniz, pderiv_X, Pi.single_apply, if_neg hv]
    simp
  have sw : ∀ a b : NSVar, ∀ q : NSAlg, pderiv a (pderiv b q) = pderiv b (pderiv a q) := by
    intro a b q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p v hp =>
      simp only [Derivation.leibniz, pderiv_X, map_add, smul_eq_mul, Pi.single_apply]
      split_ifs <;> subst_vars <;> simp [hp] <;> abel
  have e1 : ∀ k, pderiv (NSVar.u i) (X (NSVar.uD k j) * pderiv (NSVar.u k) p)
      = X (NSVar.uD k j) * pderiv (NSVar.u k) (pderiv (NSVar.u i) p) := fun k => by
    rw [hm _ (by simp), sw]
  have e2 : ∀ k, pderiv (NSVar.u i) (X (NSVar.uL k) * pderiv (NSVar.uD k j) p)
      = X (NSVar.uL k) * pderiv (NSVar.uD k j) (pderiv (NSVar.u i) p) := fun k => by
    rw [hm _ (by simp), sw]
  simp [genY2, genU, map_sum, e1, e2, -Derivation.leibniz, sw (NSVar.u i) (NSVar.y j)]
