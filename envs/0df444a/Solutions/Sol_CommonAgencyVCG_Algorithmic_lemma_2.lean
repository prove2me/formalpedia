-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:38:41.177017+00:00
-- url     : https://prove2.me/submissions/710eed97-bc30-4032-aef7-fcbd0050dee1

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1
import Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_1
import Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_2
import Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_3

open CommonAgencyVCG.Algorithmic in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) :
    (∃ t : Contract n O, IsIIVCG S t ∧ IsLL S t ∧ IsIR S t) ↔
      ∀ b, InDom S b → kCost S (aStar S b) ≤ ∑ ℓ, mBound S ℓ b := by
  constructor
  · rintro ⟨t, hI, hL, hR⟩ b hb
    have h1 := claim_2 S hS t hI hL b hb
    have h2 := (claim_1 S hS t hI).1 hR
    exact h1.trans (Finset.sum_le_sum fun ℓ _ => h2 ℓ b hb)
  · intro hk
    obtain ⟨⟨wsel, xsel, hv⟩, hgood⟩ := claim_3 S hS hk
    exact ⟨alg1 S wsel xsel, hgood wsel xsel hv⟩
