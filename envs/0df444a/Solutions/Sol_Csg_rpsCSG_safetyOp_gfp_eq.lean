-- Prove2me | solution 1 for Csg.rpsCSG_safetyOp_gfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:04.198651+00:00
-- url     : https://prove2.me/submissions/2e2550a6-dd0b-4886-a934-2c5a421b4b98

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
import Theorems.Thm_Csg_rpsVStarSafety_fixed
import Theorems.Thm_Csg_rpsVStarSafety_upper_bound
import Theorems.Thm_Csg_CSG_safetyOp_gfp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero).gfp = rpsVStarSafety :=
  rpsCSG.safetyOp_gfp_eq_of_certificate rpsSafeUnresolved rpsR_zero rpsVStarSafety
    rpsVStarSafety_fixed fun _ hb => rpsVStarSafety_upper_bound hb
end Csg
