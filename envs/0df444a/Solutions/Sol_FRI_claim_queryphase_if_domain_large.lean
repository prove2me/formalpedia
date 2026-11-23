-- Prove2me | solution 1 for FRI_claim_queryphase_if_domain_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:34:17.241083+00:00
-- url     : https://prove2.me/submissions/f3580409-4ed6-44d8-ad12-077ceb08a842

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_claim_queryphase_if_domain_large_induction
import Theorems.Thm_FRI_W_subset_domain
import Theorems.Thm_FRI_domain_zero_eq_D0
import Theorems.Thm_FRI_in_D0_of_in_W0_classical


set_option autoImplicit true

theorem _root_.solution
    {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_f_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_W_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (h_no_bad : ∀ i : Fin P.num_foldings,
        ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ∃ u_0 ∈ FRI_code P 0, ∀ x (hx : x ∈ FRI_W P f_0 T 0),
      u_0 ⟨x, FRI_W_subset_domain P f_0 T 0 hx⟩ =
      f_0 ⟨x, FRI_domain_zero_eq_D0 P ▸ FRI_W_subset_domain P f_0 T 0 hx⟩ := by
  obtain ⟨u_i, hu_i₁, hu_i₂⟩ :=
    FRI_claim_queryphase_if_domain_large_induction P f_0 T bound h_f_final h_W_large h_no_bad 0
  refine ⟨u_i, hu_i₁, fun x hx ↦ ?_⟩
  specialize hu_i₂ x hx
  unfold extend_by_zero at hu_i₂
  split_ifs at hu_i₂ <;> simp_all only [ge_iff_le, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      FRI_f, ↓reduceDIte]
  exact absurd (FRI_in_D0_of_in_W0_classical P f_0 T x hx) ‹¬x ∈ FRI_domain P 0›
