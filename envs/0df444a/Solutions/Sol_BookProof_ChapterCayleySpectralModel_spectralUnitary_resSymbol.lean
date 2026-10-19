-- Prove2me | solution 1 for BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:57:01.93932+00:00
-- url     : https://prove2.me/submissions/b21ece5e-a565-4239-b7eb-9eaff66603d9

-- Generated from ChapterCayleySpectralModel.lean — solution of BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
import Mathlib
import Definitions.Def_ChapterCayleySpectralModel
import Theorems.Thm_BookProof_ChapterCayleySpectralModel_cfcHom_resSymbol
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterCayleySpectralModel



open scoped InnerProductSpace
open MeasureTheory


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (xi : H)

set_option maxHeartbeats 1000000 in
theorem solution
    (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi))
    (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) :
    spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc
        (mulRep (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi) (resSymbol T) u)
      = ((T.res (-1) (spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc u) :
          T.domain) : H) := by

  rw [spectralUnitary_intertwines_cfc (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc
    (resSymbol T) u, cfcHom_resSymbol]
