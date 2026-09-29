-- Prove2me | solution 1 for BraidsLinksMCG.thm_1_9_artin_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-14T12:17:15.700636+00:00
-- url     : https://prove2.me/submissions/b3d18ec6-2d72-4340-9c78-d60d6224fab6

import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Theorems.Thm_BraidsLinksMCG_thm_1_9_sufficiency

open BraidsLinksMCG in
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
    refine ⟨⟨pi b, fun i => (artin_action_conj_perm n xi hxi pi hpi b i).choose, fun i => ?_⟩, ?_⟩
    · rw [← hb]
      exact (artin_action_conj_perm n xi hxi pi hpi b i).choose_spec
    · rw [← hb]
      exact artin_action_fixes_word n xi hxi b
  · rintro ⟨hconj, hword⟩
    exact thm_1_9_sufficiency n xi hxi beta hconj hword
