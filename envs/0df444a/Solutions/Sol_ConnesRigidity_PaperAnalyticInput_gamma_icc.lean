-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.gamma_icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/f253146c-4310-4d1c-be0a-199c5cfeea50

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
theorem _root_.solution (n : ℕ) : IsICC (gammaGroup n) :=
  gamma_isICC n
end ConnesRigidity.PaperAnalyticInput
