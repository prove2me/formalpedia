-- Prove2me | solution 1 for BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:15.19936+00:00
-- url     : https://prove2.me/submissions/53b06d7a-e23d-4b23-af7b-17e68051884f

-- Generated from ChapterEsaClosure.lean — solution of BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
import Mathlib
import Definitions.Def_ChapterEsaClosure
import Theorems.Thm_BookProof_EsaClosure_isSelfAdjointExtension_of_positive
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




variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {Dom : Submodule ℂ F} {T : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    (hesa : EssentiallySelfAdjointOn D T) (hA : IsPositiveSelfAdjointExtension T A) :
    Dom = clDom T ∧ ∀ (x : F) (h : x ∈ Dom) (h' : x ∈ clDom T),
      A ⟨x, h⟩ = clExt T hdense hsym ⟨x, h'⟩ :=
  isSelfAdjointExtension_unique_of_esa hesa (isSelfAdjointExtension_of_positive hA)
      ⟨fun v => ⟨coe_mem_clDom T v, clExt_extends T hdense hsym v⟩,
        clExt_symmetricOn T hdense hsym, clExt_selfAdjointCriterion T hdense hsym hesa⟩
