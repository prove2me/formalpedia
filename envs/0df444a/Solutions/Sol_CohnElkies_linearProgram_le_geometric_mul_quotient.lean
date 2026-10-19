-- Prove2me | solution 1 for CohnElkies.linearProgram_le_geometric_mul_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/e6fb57b2-5fc1-4b74-9872-a7ae65a3268d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_geometricFactor_pos
import Theorems.Thm_CohnElkies_quotientSet_bddBelow

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
    {d : ℕ} (f : Admissible d) :
    linearProgram d ≤
      (unitBallVolume d / (2 : ℝ) ^ d) * quotient f := by
  unfold linearProgram
  exact mul_le_mul_of_nonneg_left
    (csInf_le (quotientSet_bddBelow d) ⟨f, rfl⟩)
    (geometricFactor_pos d).le
end CohnElkies
