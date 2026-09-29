-- Prove2me | solution 1 for BurauFaithful.burauRep3_x
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:29:55.163103+00:00
-- url     : https://prove2.me/submissions/53623fcc-a69a-4ab4-b082-789fa406d66f

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open BurauFaithful in
theorem solution :
    (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
      BraidsLinksMCG.sigma ⟨1, by decide⟩ * BraidsLinksMCG.sigma ⟨0, by decide⟩)).1 =
      ![![1 - LaurentPolynomial.T 1,
          LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1),
          LaurentPolynomial.T 1 ^ 2],
        ![1 - LaurentPolynomial.T 1, LaurentPolynomial.T 1, 0],
        ![1, 0, 0]] := by
  simp only [map_mul, Units.val_mul]
  have hg : ∀ i : Fin (3 - 1), (burauRep 3 (BraidsLinksMCG.sigma i)).1 = burauMatrix i := by
    intro i
    have h := PresentedGroup.toGroup.of (h := burauGen_relations 3) (x := i)
    exact congrArg Units.val h
  rw [hg, hg]
  refine Matrix.ext fun a b => ?_
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, burauMatrix_apply] <;>
    first | ring1 | (simp; done) | (left; ring1) | (rw [← LaurentPolynomial.T_add]; norm_num; done)
