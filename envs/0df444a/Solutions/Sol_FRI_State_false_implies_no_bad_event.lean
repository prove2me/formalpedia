-- Prove2me | solution 1 for FRI_State_false_implies_no_bad_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:37.695606+00:00
-- url     : https://prove2.me/submissions/ed4e8c95-8f12-40bc-94cf-db49a5b3adcf

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_State_monotone


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (h_state : ¬ FRI_State P f_0 bound T P.num_foldings) :
    ∀ i : Fin P.num_foldings,
      ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by
  intro i hi
  refine h_state (FRI_State_monotone P f_0 bound T _ _ (Nat.succ_le_of_lt i.2) ?_)
  simpa only [FRI_State, Fin.is_lt, ↓reduceDIte, Fin.eta] using .inr hi
