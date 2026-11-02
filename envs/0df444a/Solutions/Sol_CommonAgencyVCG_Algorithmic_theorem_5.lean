-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:38:41.751582+00:00
-- url     : https://prove2.me/submissions/6ac13e3a-00da-48ce-86e3-e58b2f68c463

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1
import Theorems.Thm_CommonAgencyVCG_Algorithmic_lemma_2
import Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_3

open CommonAgencyVCG.Algorithmic in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing)
    (hex : ∃ t : Contract n O, IsIIVCG S t ∧ IsLL S t ∧ IsIR S t) :
    (∃ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
        ValidSel S wsel xsel) ∧
      ∀ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
        ValidSel S wsel xsel →
          IsIIVCG S (alg1 S wsel xsel) ∧ IsLL S (alg1 S wsel xsel) ∧ IsIR S (alg1 S wsel xsel) :=
  claim_3 S hS ((lemma_2 S hS).1 hex)
