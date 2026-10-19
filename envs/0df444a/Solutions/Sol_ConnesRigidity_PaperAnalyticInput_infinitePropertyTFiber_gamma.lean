-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.infinitePropertyTFiber_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/d8c81547-760e-419c-8a2b-12672b73622f

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
    input.infinitePropertyTFiber.Gamma n = gammaGroup n := rfl
end ConnesRigidity.PaperAnalyticInput
