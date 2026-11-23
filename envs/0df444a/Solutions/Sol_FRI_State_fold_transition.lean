-- Prove2me | solution 1 for FRI_State_fold_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:43.596929+00:00
-- url     : https://prove2.me/submissions/6c18faba-b920-406d-a4c9-410d63f0fa1d

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
import Theorems.Thm_FRI_State_step


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings) :
    FRI_State P f_0 bound T (i + 1) ↔
    FRI_State P f_0 bound T i ∨
      FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) :=
  FRI_State_step P f_0 bound T i i.isLt
