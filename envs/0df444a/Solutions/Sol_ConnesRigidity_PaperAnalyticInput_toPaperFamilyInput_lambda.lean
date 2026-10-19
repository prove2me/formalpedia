-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.toPaperFamilyInput_lambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/b3cd5997-d5bc-45ce-9b8b-27e0039f31f7

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
theorem _root_.solution
    (input : PaperAnalyticInput) :
    input.toPaperFamilyInput.Lambda = lambdaGroup := rfl
end ConnesRigidity.PaperAnalyticInput
