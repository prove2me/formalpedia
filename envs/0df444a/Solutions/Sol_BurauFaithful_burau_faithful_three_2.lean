-- Prove2me | solution 2 for BurauFaithful.burau_faithful_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T05:35:22.935802+00:00
-- url     : https://prove2.me/submissions/6d32b8d1-c03b-4232-92a7-bd2e5cd316c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Shorter reduction of `BurauFaithful.burau_faithful_three` (Birman, *Braids, Links, and Mapping
Class Groups*, Ann. of Math. Studies 82, 1974, §3.3, Theorem 3.15, pp. 129--130), bypassing the
word-level statement:

* `burau_three_spec_kernel`                  -- kernel of the specialization at $t=-1$;
* `burau_three_fullTwist_sq_infinite_order`  -- no nontrivial power of $\Delta^4$ dies.

Given the two, a braid killed by $\rho_3$ is a power of $\Delta^4$, and that power must be trivial.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_burau_three_spec_kernel
import Theorems.Thm_BurauFaithful_burau_three_fullTwist_sq_infinite_order

set_option autoImplicit false

/-- **Theorem 3.15 of Birman (Theorem 4.1 for three strands).** The unreduced Burau representation
`ρ₃` of the three-strand braid group is faithful. -/
theorem solution : Function.Injective (BurauFaithful.burauRep 3) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  have hφ : Matrix.GeneralLinearGroup.map (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ))
      (BurauFaithful.burauRep 3 β) = 1 := by
    rw [hβ]
    simp
  obtain ⟨k, hk⟩ := (BurauFaithful.burau_three_spec_kernel β).mp hφ
  have h1 : (BurauFaithful.burauRep 3
      (BraidsLinksMCG.sigma ⟨0, by decide⟩ * BraidsLinksMCG.sigma ⟨1, by decide⟩)) ^
        (6 * k) = 1 := by
    rw [← map_zpow, ← hk]
    exact hβ
  have hk0 : k = 0 := BurauFaithful.burau_three_fullTwist_sq_infinite_order k h1
  rw [hk, hk0, mul_zero, zpow_zero]
