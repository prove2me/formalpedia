-- Prove2me | solution 1 for FRI_State_query_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:37:02.466257+00:00
-- url     : https://prove2.me/submissions/9990301b-f107-4742-915e-0a6d7219ffec

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) :
    FRI_State P f_0 bound T (P.num_foldings + 1) ↔
    FRI_State P f_0 bound T P.num_foldings ∨ FRI_verifier_accepts P f_0 T := by
  grind [FRI_State]
