-- Prove2me | solution 1 for CubicP3Partition.kelmans_z1_iff_z8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T21:28:48.265424+00:00
-- url     : https://prove2.me/submissions/75307be5-0faa-4abe-a9ec-53844497f2a7

import Definitions.Def_cubic_p3_partition_models
import Theorems.Thm_CubicP3Partition_kelmans_z1_implies_z8
import Theorems.Thm_CubicP3Partition_kelmans_z8_implies_z1

open CubicP3Partition

theorem solution : ClaimZ1 ↔ ClaimZ8 :=
  Iff.intro kelmans_z1_implies_z8 kelmans_z8_implies_z1
