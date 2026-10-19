-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.toPaperFamilyInput_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/e1517871-c09c-400a-983b-13a25f7bdfff

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
    (input : PaperAnalyticInput) (n : ℕ) :
    input.toPaperFamilyInput.Gamma n = gammaGroup n := rfl
end ConnesRigidity.PaperAnalyticInput
