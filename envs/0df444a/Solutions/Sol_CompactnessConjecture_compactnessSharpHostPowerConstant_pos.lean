-- Prove2me | solution 1 for CompactnessConjecture.compactnessSharpHostPowerConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/97b9e45a-f1fb-4698-a4ba-f0750fc2287a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution :
    0 < compactnessSharpHostPowerConstant := by
  unfold compactnessSharpHostPowerConstant compactnessHostPowerConstant
    compactnessDegreePowerConstant
  positivity
end CompactnessConjecture
