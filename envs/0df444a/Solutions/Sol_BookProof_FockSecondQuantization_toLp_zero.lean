-- Prove2me | solution 1 for BookProof.FockSecondQuantization.toLp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:45:22.906976+00:00
-- url     : https://prove2.me/submissions/d2a4301c-fa39-4892-85d4-ae57ba92ed08

import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization

noncomputable section

theorem solution : toLp (0 : FockAlg) = 0 := by
  rfl
