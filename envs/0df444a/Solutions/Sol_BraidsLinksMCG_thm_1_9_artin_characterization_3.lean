-- Prove2me | solution 3 for BraidsLinksMCG.thm_1_9_artin_characterization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T05:43:54.470178+00:00
-- url     : https://prove2.me/submissions/7ef5a4ae-5bcf-4aa6-b0b7-34a349b9b70c

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Theorems.Thm_BraidsLinksMCG_thm_1_9_sufficiency

open BraidsLinksMCG

noncomputable section

/-- Artin's Theorem 1.9, assembled from the published ingredients.

The `⟸` direction is the published `thm_1_9_sufficiency`. The `⟹` direction reads off the two
Artin conditions from a braid that realises `beta`: the conjugacy condition is
`artin_action_conj_perm`, with the permutation supplied by `braid_perm_hom`, and the fixed-word
condition is `artin_action_fixes_word`. -/
theorem solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n)) :
    (∃ b : ArtinBraidGroup n, ∀ w : FreeGroup (Fin n), xi b w = beta w) ↔
      ((∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
            ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹) ∧
        beta (freeWordProd n) = freeWordProd n) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨pi, hpi⟩ := braid_perm_hom n
    refine ⟨⟨pi b, fun i => (artin_action_conj_perm n xi hxi pi hpi b i).choose, ?_⟩, ?_⟩
    · intro i
      rw [← hb (FreeGroup.of i)]
      exact (artin_action_conj_perm n xi hxi pi hpi b i).choose_spec
    · rw [← hb (freeWordProd n)]
      exact artin_action_fixes_word n xi hxi b
  · intro h
    exact thm_1_9_sufficiency n xi hxi beta h.1 h.2

end
