-- Prove2me | solution 1 for FRI_State_query_transition_prob
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:32.525907+00:00
-- url     : https://prove2.me/submissions/284fa576-d45c-4155-b856-7c85d56457ee

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
import Theorems.Thm_FRI_State_query_transition

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (h_state_0 : ¬ FRI_State P f_0 bound T P.num_foldings) :
    FRI_State P f_0 bound T (P.num_foldings + 1) ↔ FRI_verifier_accepts P f_0 T :=
  (FRI_State_query_transition P f_0 bound T).trans (or_iff_right h_state_0)
