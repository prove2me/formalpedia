-- Prove2me | solution 1 for FRI_in_D0_of_in_W0_classical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:28:38.768713+00:00
-- url     : https://prove2.me/submissions/bfebb1b3-5f98-4947-8c7d-3721ca7f51f5

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_W_subset_D0

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (x : F) (hx : x ∈ FRI_W P f_0 T 0) : x ∈ P.D_0 :=
  FRI_W_subset_D0 P f_0 T hx
