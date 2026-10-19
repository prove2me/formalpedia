-- Prove2me | solution 1 for BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:01:19.744852+00:00
-- url     : https://prove2.me/submissions/2183036c-48c9-45c4-89c8-38f859240094

-- Generated from ChapterStoneEigenflow.lean — solution of BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector
import Mathlib
import Definitions.Def_ChapterStoneEigenflow
import Theorems.Thm_BookProof_StoneEigenflow_isSelfAdjointExtension_eigenvector
import Theorems.Thm_BookProof_StoneEigenflow_stoneFlow_apply_eigenvector
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.StoneEigenflow



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.EsaClosure BookProof.FarisLavine
open BookProof.ChapterStoneResolvent BookProof.StoneBridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)}
    (hext : IsSelfAdjointExtension Hc T.op) (hU : IsStoneFlow T U) (x : D) {lam : ℝ}
    (hx : Hc x = (lam : ℂ) • (x : F)) (t : ℝ) :
    U t (x : F) = Complex.exp (-(Complex.I * lam * t)) • (x : F) := by

  obtain ⟨hmem, heq⟩ := isSelfAdjointExtension_eigenvector hext x hx
  exact stoneFlow_apply_eigenvector hU hmem heq t
