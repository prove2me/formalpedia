-- Prove2me | solution 1 for CubicP3Partition.kelmans_z8_implies_z1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T21:33:06.221428+00:00
-- url     : https://prove2.me/submissions/36176c43-f545-4341-9df1-2f9c70454455

import Definitions.Def_cubic_p3_partition_models
import Theorems.Thm_CubicP3Partition_kelmans_admissible_has_p3path
import Theorems.Thm_CubicP3Partition_kelmans_p3_factor_extend

open CubicP3Partition

theorem solution : ClaimZ8 → ClaimZ1 := by
  intro h8 W hFin G hCub hCon hCard
  obtain ⟨L⟩ := kelmans_admissible_has_p3path W G hCub hCon hCard
  exact kelmans_p3_factor_extend W G L (h8 W G hCub hCon hCard L)
