-- Prove2me | solution 1 for FRI_verifier_accepts_iff_s_in_W0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:33:41.617589+00:00
-- url     : https://prove2.me/submissions/f4a934d5-53d0-41d7-a172-289a5e54dcc5

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (h_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings) :
    FRI_verifier_accepts P f_0 T ↔ ∀ j : Fin P.q_rep, (T.s j).val ∈ FRI_W P f_0 T 0 := by
  simp only [FRI_verifier_accepts, h_final, true_and, FRI_W, FRI_BadQuery_Points]
  grind
