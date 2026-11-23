-- Prove2me | solution 1 for Csg.idsGameCSG_reachOp_lfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:02:37.898708+00:00
-- url     : https://prove2.me/submissions/acda01c3-33d4-4721-8917-6344c1088cd8

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsVStar_fixed
import Theorems.Thm_Csg_idsVStar_le_of_prefixed
import Theorems.Thm_Csg_CSG_reachOp_lfp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero).lfp = idsVStar :=
  idsGameCSG.reachOp_lfp_eq_of_certificate idsGoalHealthy idsGameCSG_r_zero idsVStar idsVStar_fixed
    fun _ hb => idsVStar_le_of_prefixed hb
end Csg
