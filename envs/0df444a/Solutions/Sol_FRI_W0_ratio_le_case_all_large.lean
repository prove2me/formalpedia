-- Prove2me | solution 1 for FRI_W0_ratio_le_case_all_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:58.381799+00:00
-- url     : https://prove2.me/submissions/8c227521-1504-4c01-98d2-a73a1c7596f2

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_relDistance_le_of_agree_on_subset
import Theorems.Thm_FRI_claim_queryphase_if_domain_large
import Theorems.Thm_FRI_distance_star_le_relDistanceToSet
import Theorems.Thm_FRI_W_subset_domain


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_all_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (h_no_bad : ∀ i : Fin P.num_foldings,
      ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ((FRI_W P f_0 T 0).card : ℝ) / (FRI_domain P 0).card ≤ 1 - FRI_distance_star P f_0 bound := by
  -- By FRI_claim_queryphase_if_domain_large, f_0 agrees with a codeword u_0 on W_0
  obtain ⟨u_0, hu_0_in_code, hu_0_agree⟩ :=
    FRI_claim_queryphase_if_domain_large P f_0 T bound h_pass h_all_large h_no_bad
  -- Note: FRI_domain P 0 = P.D_0 definitionally
  -- Define u_0' on P.D_0 by casting
  let u_0' : P.D_0 → F := fun x ↦ u_0 ⟨x.val, x.property⟩
  -- Step 1: f_0 agrees with u_0' on W_0, so relDistance f_0 u_0' ≤ 1 - |W_0|/|D_0|
  -- Build the agreement set as a Finset of P.D_0 elements
  let W0_as_D0 : Finset P.D_0 := (FRI_W P f_0 T 0).attach.image
    (fun x ↦ ⟨x.val, FRI_W_subset_domain P f_0 T 0 x.property⟩)
  have h_card_eq : W0_as_D0.card = (FRI_W P f_0 T 0).card := by
    simp only [W0_as_D0]
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · exact fun a b hab ↦ Subtype.ext <| Subtype.mk.injEq .. ▸ hab
  have h_agree_on_W0 : ∀ x ∈ W0_as_D0, f_0 x = u_0' x := by
    intro ⟨xv, hxv⟩ hx
    simp only [W0_as_D0, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists, Subtype.mk.injEq] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hzeq : z = xv := congrArg Subtype.val hzx
    subst hzeq
    exact (hu_0_agree z hz).symm
  have h_dist_le : relDistance f_0 u_0' ≤ 1 - (W0_as_D0.card : ℝ) / Fintype.card P.D_0 :=
    relDistance_le_of_agree_on_subset f_0 u_0' W0_as_D0 h_agree_on_W0
  rw [h_card_eq, show (Fintype.card P.D_0 : ℝ) = (FRI_domain P 0).card by simp [FRI_domain]]
    at h_dist_le
  -- Step 2: Bound relDistanceToSet by relDistance to u_0'
  have h_dist_to_set : relDistanceToSet f_0 (FRI_code P 0).carrier ≤ relDistance f_0 u_0' :=
    csInf_le ⟨0, fun _ ⟨_, _, h⟩ ↦ h ▸ by unfold relDistance; positivity⟩ ⟨u_0', hu_0_in_code, rfl⟩
  -- Combine the bounds
  have h_delta_star_le := FRI_distance_star_le_relDistanceToSet P f_0 bound
  grind
