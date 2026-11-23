-- Prove2me | solution 1 for FRI_State_Transition_Prob_Fold_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:01.063979+00:00
-- url     : https://prove2.me/submissions/6509f4a9-bc32-438d-986c-6c61a41cdfc4

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution [Fintype F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (i : Fin P.num_foldings)
    (h_state_0 : ¬ FRI_State P f_0 bound T i) :
    FRI_State_Transition_Prob_Fold P f_0 bound T i =
      FRI_BadEvent_Prob P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) :=
  if_neg h_state_0
