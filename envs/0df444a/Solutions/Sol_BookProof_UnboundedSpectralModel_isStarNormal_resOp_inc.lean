-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:09.172393+00:00
-- url     : https://prove2.me/submissions/39e4a390-0997-4110-8874-d243551078af

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc
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
theorem solution (T : UnboundedSelfAdjoint H) : IsStarNormal (resOp T) := by

  constructor
  have hstar : star (resOp T) = T.resCLM (-1) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact adjoint_resCLM T one_ne_zero
  refine ContinuousLinearMap.ext fun y => ?_
  rw [hstar]
  simp only [ContinuousLinearMap.mul_apply]
  exact T.res_comm (l := -1) (m := 1) (by norm_num) one_ne_zero y
