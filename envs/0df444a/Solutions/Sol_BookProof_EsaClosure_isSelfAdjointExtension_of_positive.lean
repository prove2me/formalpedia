-- Prove2me | solution 1 for BookProof.EsaClosure.isSelfAdjointExtension_of_positive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:50:11.339559+00:00
-- url     : https://prove2.me/submissions/4b8392b1-3b7c-4ed4-bd73-0fc7692e237b

-- Generated from ChapterEsaClosure.lean — solution of BookProof.EsaClosure.isSelfAdjointExtension_of_positive
import Mathlib
import Definitions.Def_ChapterEsaClosure
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
open BookProof.EsaClosure




open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {D Dom : Submodule ℂ F} {H : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsPositiveSelfAdjointExtension H A) : IsSelfAdjointExtension H A := ⟨h.1, h.2.1, h.2.2.2⟩
