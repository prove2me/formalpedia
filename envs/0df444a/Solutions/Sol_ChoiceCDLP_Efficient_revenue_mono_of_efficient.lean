-- Prove2me | solution 1 for ChoiceCDLP.Efficient.revenue_mono_of_efficient
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:52:21.989258+00:00
-- url     : https://prove2.me/submissions/d77bb28c-b5cd-4df6-9328-ea96cf9ae53f

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_IsEfficient

open ChoiceCDLP.Efficient in
theorem solution {m n : ℕ} (N : ChoiceNetwork m n)
    (S₁ S₂ : Finset (Fin n)) (h₁ : IsEfficient N S₁) (h₂ : IsEfficient N S₂)
    (hQ : consumption N S₁ ≤ consumption N S₂) :
    revenue N S₁ ≤ revenue N S₂ := by
  by_contra hlt
  push_neg at hlt
  apply h₂
  refine ⟨fun S => if S = S₁ then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro S
    by_cases h : S = S₁ <;> simp [h]
  · simp
  · simpa [ite_mul] using hlt
  · simpa [ite_smul] using hQ
