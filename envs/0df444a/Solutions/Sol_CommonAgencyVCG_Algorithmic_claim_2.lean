-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:35:24.781166+00:00
-- url     : https://prove2.me/submissions/4d966868-493b-4d87-8d83-8107a4750925

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace Aux_CAVCG_claim2

open CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

lemma E_sum (S : Setting n A O) (a : A) (b : Fin n → O → ℝ) :
    E S a (∑ ℓ, b ℓ) = ∑ ℓ, E S a (b ℓ) := by
  unfold E
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

end Aux_CAVCG_claim2

open CommonAgencyVCG.Algorithmic Aux_CAVCG_claim2 in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) (t : Contract n O) (ht : IsIIVCG S t)
    (hLL : IsLL S t) (b : Fin n → O → ℝ) (hb : InDom S b) :
    kCost S (aStar S b) ≤ ∑ ℓ, E S (aStar S b) (t b ℓ) := by
  have hW : (∑ ℓ, t b ℓ) ∈ implSet S (aStar S b) := by
    refine ⟨fun o => ?_, fun a' => ?_⟩
    · rw [Finset.sum_apply]
      exact Finset.sum_nonneg (fun ℓ _ => hLL b hb ℓ o)
    · have h1 := (ht.1 b hb).1 a'
      unfold agentUtil at h1
      rw [E_sum, E_sum]
      exact h1
  have hbdd : BddBelow (Set.range fun w : implSet S (aStar S b) => E S (aStar S b) w) := by
    refine ⟨0, ?_⟩
    rintro x ⟨⟨w, hw⟩, rfl⟩
    unfold E
    exact Finset.sum_nonneg (fun o _ => mul_nonneg (hS.2.2.1 _ o) (hw.1 o))
  have := ciInf_le hbdd ⟨_, hW⟩
  unfold kCost
  rw [← E_sum]
  exact this
