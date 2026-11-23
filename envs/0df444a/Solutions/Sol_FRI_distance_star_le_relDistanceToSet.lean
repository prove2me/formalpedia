-- Prove2me | solution 1 for FRI_distance_star_le_relDistanceToSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:35:40.531917+00:00
-- url     : https://prove2.me/submissions/a71e1c73-5980-43fe-916a-7f83720afd86

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) :
    FRI_distance_star P f_0 bound ≤ relDistanceToSet f_0 (FRI_code P 0).carrier :=
  min_le_left ..
