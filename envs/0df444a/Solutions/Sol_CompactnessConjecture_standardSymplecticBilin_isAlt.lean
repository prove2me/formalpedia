-- Prove2me | solution 1 for CompactnessConjecture.standardSymplecticBilin_isAlt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/d8c75081-0394-447e-b763-10cb92a484a6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution :
    (standardSymplecticBilin K).IsAlt := by
  intro u
  exact standardSymplecticForm_self K u
end CompactnessConjecture
