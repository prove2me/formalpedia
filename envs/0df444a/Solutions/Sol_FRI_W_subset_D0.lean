-- Prove2me | solution 1 for FRI_W_subset_D0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:35.134284+00:00
-- url     : https://prove2.me/submissions/24ef3fd7-b11b-40ab-8d08-4358e6f6e910

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) :
    FRI_W P f_0 T 0 ⊆ P.D_0 := by grind [FRI_W]
