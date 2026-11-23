-- Prove2me | solution 1 for FRI_agreement_at_round_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:15.547604+00:00
-- url     : https://prove2.me/submissions/47c0298e-1c16-4cdd-8f4f-0474f7c028c8

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_agreement_propagation
import Theorems.Thm_FRI_agreement_at_round_base_case
import Theorems.Thm_FRI_State_false_implies_no_bad_event

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_large : ∀ i (h : i < P.num_foldings),
        FRI_Is_Large_Subset P f_0 bound i h (FRI_green_set P f_0 T i)) :
    FRI_agreement_at_round P f_0 T 0 := by
  suffices h_agree_all : ∀ i : Fin (P.num_foldings + 1), FRI_agreement_at_round P f_0 T i from
    h_agree_all 0
  intro i
  induction i using Fin.reverseInduction with
  | last => exact FRI_agreement_at_round_base_case P f_0 T h_final
  | cast i ih =>
    exact FRI_agreement_propagation P f_0 bound T i
      (FRI_State_false_implies_no_bad_event P f_0 bound T h_state i) (h_large _ i.2) ih
