-- Prove2me | solution 1 for FRI_State_Transition_Prob_Query_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:21.238452+00:00
-- url     : https://prove2.me/submissions/933fa3e8-e085-48ef-abd5-46d8886241c5

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_state_0 : ¬ FRI_State P f_0 bound T P.num_foldings) :
    FRI_State_Transition_Prob_Query P f_0 bound T = FRI_query_prob P f_0 bound T := by
  simp only [FRI_State_Transition_Prob_Query, if_neg h_state_0]
