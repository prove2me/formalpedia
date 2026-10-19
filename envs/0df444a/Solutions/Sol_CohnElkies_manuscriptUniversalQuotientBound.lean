-- Prove2me | solution 1 for CohnElkies.manuscriptUniversalQuotientBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/ffc21e35-a212-4038-8620-42de1dc4d454

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscriptPackingRoot_sub_deficit_pow_le
import Theorems.Thm_CohnElkies_linearProgram_le_geometric_mul_quotient

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (f : Admissible d) :
    (2 : ℝ) ^ d / unitBallVolume d *
        (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      quotient f := by
  have hprogram :=
    (manuscriptPackingRoot_sub_deficit_pow_le hd).trans
      (linearProgram_le_geometric_mul_quotient f)
  calc
    (2 : ℝ) ^ d / unitBallVolume d *
        (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      (2 : ℝ) ^ d / unitBallVolume d *
        ((unitBallVolume d / (2 : ℝ) ^ d) * quotient f) := by
          exact mul_le_mul_of_nonneg_left hprogram
            (div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) d)
              (unitBallVolume_pos d)).le
    _ = quotient f := by
      have hv := (unitBallVolume_pos d).ne'
      field_simp
end CohnElkies
