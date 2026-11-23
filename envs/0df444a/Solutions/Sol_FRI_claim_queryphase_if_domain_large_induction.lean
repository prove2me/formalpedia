-- Prove2me | solution 1 for FRI_claim_queryphase_if_domain_large_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:32:24.771455+00:00
-- url     : https://prove2.me/submissions/5402611e-99bb-4ff0-9cb1-6201f20aa954

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_W_is_large
import Theorems.Thm_FRI_W_subset_domain
import Theorems.Thm_FRI_fold_agreement_on_W
import Theorems.Thm_FRI_induction_step


set_option autoImplicit true

theorem _root_.solution
    {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_f_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_W_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (h_no_bad : ∀ i : Fin P.num_foldings,
        ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ∀ i : Fin (P.num_foldings + 1), ∃ u ∈ FRI_code P i, ∀ x ∈ FRI_W P f_0 T i,
      extend_by_zero (FRI_domain P i) (FRI_f P f_0 T i) x =
        extend_by_zero (FRI_domain P i) u x := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact ⟨FRI_final_oracle P f_0 T, h_f_final, fun _ _ ↦ by simp [FRI_f, FRI_final_oracle]⟩
  | cast i ih =>
    obtain ⟨u, hu₁, hu₂⟩ := ih
    refine FRI_induction_step P f_0 T bound i ?_ u hu₁ ?_ (h_no_bad i)
    · exact FRI_W_is_large P f_0 T bound h_W_large i
    · intro z hz
      have h_fold := FRI_fold_agreement_on_W P f_0 T i z hz
      simp_rw [Fin.val_succ] at hu₂
      have h_z_in_domain := FRI_W_subset_domain P f_0 T (↑i + 1) hz
      simp only [h_fold, extend_by_zero, h_z_in_domain, ↓reduceDIte]
      simpa [extend_by_zero, FRI_f, h_z_in_domain] using hu₂ z hz
