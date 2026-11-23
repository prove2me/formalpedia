-- Prove2me | solution 1 for FRI_accepting_set_eq_bad_query_sequences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:26.407253+00:00
-- url     : https://prove2.me/submissions/1c977740-b1f4-4053-96ef-0b3d45c0066d

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_verifier_accepts_iff_s_in_W0
import Theorems.Thm_FRI_State_independent_of_s
import Theorems.Thm_FRI_State_succ_iff_verifier_accepts

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (bound : ℝ) (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings) :
    {s : Fin P.q_rep → { x // x ∈ P.D_0 } |
      let T' := { T with s := s }
      FRI_State P f_0 bound T' (P.num_foldings + 1)} =
    {s : Fin P.q_rep → { x // x ∈ P.D_0 } | ∀ j : Fin P.q_rep, (s j).val ∈ FRI_W P f_0 T 0} := by
  ext s
  simp only [Set.mem_setOf_eq]
  have h_state_s :=
    (FRI_State_independent_of_s P f_0 bound T.f T.alpha s T.s P.num_foldings
      (Nat.le_refl P.num_foldings)).not.mpr h_state
  exact (FRI_State_succ_iff_verifier_accepts P f_0 bound
    { f := T.f, alpha := T.alpha, s := s } h_state_s).trans
    (FRI_verifier_accepts_iff_s_in_W0 P f_0 { f := T.f, alpha := T.alpha, s := s } h_pass)
