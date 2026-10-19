-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.gamma_propertyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/1d5dad02-f11c-4ccf-9886-1051cb634bd8

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
theorem _root_.solution (input : PaperAnalyticInput) (n : ℕ) :
    HasKazhdanPropertyT (gammaGroup n) :=
  gamma_hasKazhdanPropertyT_unconditional n input.universalLattice
end ConnesRigidity.PaperAnalyticInput
