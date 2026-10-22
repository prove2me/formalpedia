-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.model_apply_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:14.395986+00:00
-- url     : https://prove2.me/submissions/7e9e944a-d3b8-43d9-8267-44a800a163ca

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.model_apply_inc
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
variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

set_option maxHeartbeats 1000000 in
theorem solution (u : Lp ℂ 2 mu) :
    T.op ⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩
      = V (u + Complex.I • mulRep mu (coordFn (resOp T)) u) := by

  have hsub : (⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩ : T.domain)
      = ⟨resOp T (V u), resOp_mem T (V u)⟩ := Subtype.ext (hV u)
  rw [hsub, op_resOp, map_add, map_smul, hV u]
