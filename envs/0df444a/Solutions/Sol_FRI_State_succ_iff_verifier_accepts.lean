-- Prove2me | solution 1 for FRI_State_succ_iff_verifier_accepts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:12:03.144802+00:00
-- url     : https://prove2.me/submissions/d25760ed-b889-4788-aadd-153a39a25106

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings) :
    FRI_State P f_0 bound T (P.num_foldings + 1) ↔ FRI_verifier_accepts P f_0 T := by
  rw [FRI_State]
  grind
