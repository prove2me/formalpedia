-- Prove2me | solution 1 for CerednikDrinfeld.exists_torsionFree_surjective_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2815429b-abe8-5fa2-af21-2b03cf3450af

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq

set_option autoImplicit false

theorem solution
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B] (h : S →+* B) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T) (q : T →+* B),
      (∀ t : T, (p : T) * t = 0 → t = 0) ∧ Function.Surjective q ∧ q.comp i = h := by
  classical
  refine ⟨MvPolynomial B S, inferInstance, MvPolynomial.C, MvPolynomial.eval₂Hom h id, ?_, ?_, ?_⟩
  · intro t ht
    have hC : (p : MvPolynomial B S) = MvPolynomial.C (p : S) := by simp
    rw [hC, MvPolynomial.C_mul'] at ht
    ext m
    have hm := congrArg (MvPolynomial.coeff m) ht
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, smul_eq_mul] at hm
    rw [MvPolynomial.coeff_zero]
    exact hS _ hm
  · intro b
    exact ⟨MvPolynomial.X b, by simp⟩
  · ext s
    simp

end S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq (solution)
