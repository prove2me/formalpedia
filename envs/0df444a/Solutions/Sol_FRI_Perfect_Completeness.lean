-- Prove2me | solution 1 for FRI_Perfect_Completeness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:48:24.944284+00:00
-- url     : https://prove2.me/submissions/f1248450-2712-42e9-9e6c-b5e77118628c

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_honest_transcript_all_in_code
import Theorems.Thm_honest_transcript_local_checks

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F)
    (f_0 : P.D_0 → F)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier) :
    ∀ (challenges : FRIVerifierChallenges P),
      let T := FRI_honest_transcript P f_0 challenges
      FRI_verifier_accepts P f_0 T := by
  refine fun c ↦ ⟨?_, honest_transcript_local_checks P f_0 c _ rfl⟩
  simp only [FRI_final_oracle]
  split_ifs with h <;>
    simp_all only [Submodule.carrier_eq_coe, SetLike.mem_coe, FRI_honest_transcript, Fin.succ_mk]
  · cases P; simp only at h ⊢; subst h; exact h_f0_in_code
  · convert honest_transcript_all_in_code P f_0 h_f0_in_code c ⟨P.num_foldings, _⟩
    all_goals omega
