-- Prove2me | solution 1 for BookProof.StoneEigenflow.exists_diagonal_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:11:58.168548+00:00
-- url     : https://prove2.me/submissions/bdff9afe-a554-43a7-a289-9786aa57f026

-- Generated from ChapterStoneEigenflow.lean — solution of BookProof.StoneEigenflow.exists_diagonal_stone_flow
import Mathlib
import Definitions.Def_ChapterStoneEigenflow
import Theorems.Thm_BookProof_StoneEigenflow_stoneFlow_apply_core_eigenvector
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.StoneEigenflow



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.EsaClosure BookProof.FarisLavine
open BookProof.ChapterStoneResolvent BookProof.StoneBridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] {D : Submodule ℂ F} (Hc : D →ₗ[ℂ] F)
    (hdense : Dense ((D : Submodule ℂ F) : Set F)) (hsym : SymmetricOn D Hc)
    (hesa : EssentiallySelfAdjointOn D Hc) {ι : Type*} (psi : ι → D) (lam : ι → ℝ)
    (hev : ∀ α, Hc (psi α) = ((lam α : ℝ) : ℂ) • ((psi α : F))) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      IsSelfAdjointExtension Hc T.op ∧ IsStoneFlow T U ∧
        ∀ (α : ι) (t : ℝ),
          U t ((psi α : F)) = Complex.exp (-(Complex.I * lam α * t)) • ((psi α : F)) := by

  obtain ⟨T, U, hext, hU⟩ := exists_stone_flow_of_esa Hc hdense hsym hesa
  exact ⟨T, U, hext, hU, fun α t =>
    stoneFlow_apply_core_eigenvector hext hU (psi α) (hev α) t⟩
