-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.adjoint_resCLM_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:01.822519+00:00
-- url     : https://prove2.me/submissions/78fc347c-e9d4-4972-bf0b-723177ec49d9

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.adjoint_resCLM_inc
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel



noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) :
    ContinuousLinearMap.adjoint (T.resCLM l) = T.resCLM (-l) := by

  refine ((ContinuousLinearMap.eq_adjoint_iff (T.resCLM (-l)) (T.resCLM l)).mpr ?_).symm
  intro y z
  simpa using T.inner_res (l := -l) (neg_ne_zero.mpr hl) y z
