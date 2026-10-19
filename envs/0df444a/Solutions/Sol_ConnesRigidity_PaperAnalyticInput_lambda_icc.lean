-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.lambda_icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/a3cd86d3-a853-4d50-80d9-95fd4928ad76

import Mathlib
import Definitions.Def_ConnesRigidity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
open ConnesRigidity
open ConnesRigidity.PaperAnalyticInput
namespace ConnesRigidity.PaperAnalyticInput
theorem _root_.solution : IsICC lambdaGroup :=
  lambda_isICC
end ConnesRigidity.PaperAnalyticInput
