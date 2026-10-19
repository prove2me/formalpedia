-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.infinitePropertyTFiber_lambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/f489add6-aedf-49f5-bdd8-20cbf1f2f960

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
    input.infinitePropertyTFiber.Lambda = lambdaGroup := rfl
end ConnesRigidity.PaperAnalyticInput
