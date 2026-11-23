-- Prove2me | solution 1 for FRI_State_fold_transition_prob
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:28.606799+00:00
-- url     : https://prove2.me/submissions/335330c6-1e52-484c-9974-d96095fc5445

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
import Theorems.Thm_FRI_State_fold_transition

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings)
    (h_state_0 : ¬ FRI_State P f_0 bound T i) :
    FRI_State P f_0 bound T (i + 1) ↔
    FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by
  simp only [FRI_State_fold_transition, h_state_0, false_or]
