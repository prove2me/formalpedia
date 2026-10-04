-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.quadForm_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:09:36.526685+00:00
-- url     : https://prove2.me/submissions/c84733bc-e5a5-4860-a2e0-137a50b70825

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavineCore

set_option autoImplicit false

open BookProof.FarisLavine in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {D D' : Submodule ℂ F} (N : D →ₗ[ℂ] F) (N' : D' →ₗ[ℂ] F)
    (x : D) (x' : D') (hx : (x : F) = (x' : F)) (hN : N x = N' x') :
    quadForm N x = quadForm N' x' := by
  unfold quadForm
  rw [hx, hN]
