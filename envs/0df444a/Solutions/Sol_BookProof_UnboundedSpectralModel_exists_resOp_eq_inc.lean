-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.exists_resOp_eq_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:07.670967+00:00
-- url     : https://prove2.me/submissions/5b555595-d0c1-416e-8c53-5b934a2162c4

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.exists_resOp_eq_inc
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
theorem solution (T : UnboundedSelfAdjoint H) {x : H} (hx : x ∈ T.domain) :
    ∃ y : H, resOp T y = x := by

  refine ⟨T.shift 1 ⟨x, hx⟩, ?_⟩
  have h := T.res_shift (l := 1) one_ne_zero ⟨x, hx⟩
  have := congrArg (fun w : T.domain => (w : H)) h
  simpa [resOp, UnboundedSelfAdjoint.resCLM_apply] using this
