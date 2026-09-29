-- Prove2me | solution 2 for BraidsLinksMCG.thm_1_9_artin_characterization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:08:26.790325+00:00
-- url     : https://prove2.me/submissions/69784e1c-0de0-4f4b-bf55-5d1a4255acc7

import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Theorems.Thm_BraidsLinksMCG_thm_1_9_sufficiency
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n)) :
    (∃ b : ArtinBraidGroup n, ∀ w : FreeGroup (Fin n), xi b w = beta w) ↔
      ((∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
            ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹) ∧
        beta (freeWordProd n) = freeWordProd n) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨pi, hpi⟩ := BraidsLinksMCG.braid_perm_hom n
    refine ⟨⟨pi b,
      fun i => (BraidsLinksMCG.artin_action_conj_perm n xi hxi pi hpi b i).choose, ?_⟩, ?_⟩
    · intro i
      rw [← hb (FreeGroup.of i)]
      exact (BraidsLinksMCG.artin_action_conj_perm n xi hxi pi hpi b i).choose_spec
    · rw [← hb (freeWordProd n)]
      exact BraidsLinksMCG.artin_action_fixes_word n xi hxi b
  · rintro ⟨hconj, hword⟩
    exact BraidsLinksMCG.thm_1_9_sufficiency n xi hxi beta hconj hword

#print axioms solution
