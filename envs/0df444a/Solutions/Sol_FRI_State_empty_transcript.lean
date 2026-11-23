-- Prove2me | solution 1 for FRI_State_empty_transcript
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:40.306034+00:00
-- url     : https://prove2.me/submissions/0096a415-829a-432a-bb80-d0da18e9394e

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) :
    FRI_State P f_0 bound T 0 ↔ f_0 ∈ (FRI_code P 0).carrier := by
  rfl
