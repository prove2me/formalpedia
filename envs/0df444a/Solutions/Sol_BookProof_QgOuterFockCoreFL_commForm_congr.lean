-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.commForm_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:43:06.416491+00:00
-- url     : https://prove2.me/submissions/259382e8-5217-4723-af13-1d83d9e08fbd

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavineCore

set_option autoImplicit false

universe u_1

open BookProof.QgOuterFockCoreFL BookProof.FarisLavine BookProof.DirectSumEsa BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.YangMillsFriedrichs BookProof.EsaClosure BookProof.QgHermiteOscillator BookProof.HermiteProductCore Filter Topology in
theorem solution {F : Type u_1} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {D D' : Submodule ℂ F} (H N : D →ₗ[ℂ] F) (H' N' : D' →ₗ[ℂ] F)
    (x : D) (x' : D') (hH : H x = H' x') (hN : N x = N' x') :
    commForm H N x = commForm H' N' x' := by
  simp only [commForm, hH, hN]
