-- Prove2me | solution 1 for CubicP3Partition.kelmans_z1_implies_z8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T23:24:51.414076+00:00
-- url     : https://prove2.me/submissions/14362d6d-79c5-4fbe-812b-2bef7ffdf361

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_kelmans_aux_claims
import Theorems.Thm_CubicP3Partition_kelmans_z1_implies_z4
import Theorems.Thm_CubicP3Partition_kelmans_z4_implies_t2
import Theorems.Thm_CubicP3Partition_kelmans_t2_implies_z7
import Theorems.Thm_CubicP3Partition_kelmans_z7_implies_z8

open CubicP3Partition

theorem solution : ClaimZ1 -> ClaimZ8 :=
  fun h1 => kelmans_z7_implies_z8 (kelmans_t2_implies_z7 (kelmans_z4_implies_t2 (kelmans_z1_implies_z4 h1)))
