-- Prove2me | solution 1 for CohnElkies.saddleSourceFirstBranchVarianceCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/5193e834-2321-4bda-b7e3-838cda53a49e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourcePositiveShellVariance_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε) :
    0 < saddleSourceFirstBranchVarianceCoefficient ε := by
  have hshell :=
    saddleSourcePositiveShellVariance_nonneg ε (ε / 2)
  unfold saddleSourceFirstBranchVarianceCoefficient
  nlinarith [mul_nonneg
    (show 0 ≤ 2 + ε / 2 by positivity) hshell]
end CohnElkies
