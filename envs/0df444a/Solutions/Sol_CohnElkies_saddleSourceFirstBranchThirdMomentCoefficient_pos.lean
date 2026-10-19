-- Prove2me | solution 1 for CohnElkies.saddleSourceFirstBranchThirdMomentCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/d62e1be7-6d4b-48c8-a4b9-a0d9a78d7301

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourcePositiveShellThirdMoment_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    0 < saddleSourceFirstBranchThirdMomentCoefficient ε := by
  have hcut : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hA : 0 ≤ shortEndpoint ε :=
    (hcut.trans_le horder).le
  have hremote :=
    saddleSourcePositiveShellThirdMoment_nonneg hε (ε / 2)
  unfold saddleSourceFirstBranchThirdMomentCoefficient
  positivity
end CohnElkies
