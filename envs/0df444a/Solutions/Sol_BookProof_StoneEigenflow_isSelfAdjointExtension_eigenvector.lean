-- Prove2me | solution 1 for BookProof.StoneEigenflow.isSelfAdjointExtension_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:01:18.658169+00:00
-- url     : https://prove2.me/submissions/859ab1f1-35a0-47af-98c6-fab2fbc8242f

-- Generated from ChapterStoneEigenflow.lean — solution of BookProof.StoneEigenflow.isSelfAdjointExtension_eigenvector
import Mathlib
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.StoneEigenflow



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.EsaClosure BookProof.FarisLavine
open BookProof.ChapterStoneResolvent BookProof.StoneBridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsSelfAdjointExtension Hc A) (x : D) {lam : ℂ}
    (hx : Hc x = lam • (x : F)) :
    ∃ hmem : (x : F) ∈ Dom, A ⟨(x : F), hmem⟩ = lam • (x : F) := by

  obtain ⟨hmem, heq⟩ := h.1 x
  exact ⟨hmem, by rw [heq, hx]⟩
