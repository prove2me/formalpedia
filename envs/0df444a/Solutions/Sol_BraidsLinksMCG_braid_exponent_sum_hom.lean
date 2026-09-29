-- Prove2me | solution 1 for BraidsLinksMCG.braid_exponent_sum_hom
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-14T12:09:55.79811+00:00
-- url     : https://prove2.me/submissions/7c980466-6e81-4216-bc3c-a540b88ccf58

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

open BraidsLinksMCG in
theorem solution (n : ℕ) :
    ∃ eps : ArtinBraidGroup n →* Multiplicative ℤ,
      ∀ i : Fin (n - 1), eps (sigma i) = Multiplicative.ofAdd (1 : ℤ) := by
  have hrel : ∀ r ∈ braidRels n,
      (FreeGroup.lift fun _ : Fin (n - 1) => (Multiplicative.ofAdd (1 : ℤ))) r = 1 := by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩) <;>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of] <;> group
  exact ⟨PresentedGroup.toGroup hrel, fun i => PresentedGroup.toGroup.of hrel⟩
