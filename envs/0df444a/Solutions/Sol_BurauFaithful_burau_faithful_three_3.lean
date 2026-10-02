-- Prove2me | solution 3 for BurauFaithful.burau_faithful_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T14:51:04.250986+00:00
-- url     : https://prove2.me/submissions/5bd6ac48-3e8c-45ec-bf3e-02ff4fed4a0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_burau_three_spec_kernel_hard
import Theorems.Thm_BurauFaithful_burau_three_fullTwist_sq_infinite_order

set_option autoImplicit false

open Matrix BraidsLinksMCG

/-- The milestone target `BurauFaithful.burau_faithful_three`, reduced to the description of the
kernel of the `t = -1` specialization of the unreduced Burau representation together with the fact
that the image of the full twist squared has infinite order. -/
theorem solution : Function.Injective (BurauFaithful.burauRep 3) := by
  rw [injective_iff_map_eq_one]
  intro beta hbeta
  have h1 : (Matrix.GeneralLinearGroup.map
      (LaurentPolynomial.eval₂ (Int.castRingHom Int) (-1 : Intˣ))
      (BurauFaithful.burauRep 3 beta)) = 1 := by
    rw [hbeta, map_one]
  obtain ⟨k, hk⟩ := BurauFaithful.burau_three_spec_kernel_hard beta h1
  have htwist : (BurauFaithful.burauRep 3
      (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩)) ^ (6 * k) = 1 := by
    rw [← map_zpow]
    rw [← hk]
    exact hbeta
  have hk0 : k = 0 := BurauFaithful.burau_three_fullTwist_sq_infinite_order k htwist
  rw [hk, hk0, mul_zero, zpow_zero]
