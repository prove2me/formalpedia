-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:05:33.423438+00:00
-- url     : https://prove2.me/submissions/341bd30d-f3f7-4845-ba75-a6cc3ee12b69

import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_esa_of_farisLavine
set_option autoImplicit false

open Filter Topology MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.DiffHashimoto
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem solution {Dom₁ Dom₂ : Submodule ℂ (L2d 3)}
    {G₁ : Dom₁ →ₗ[ℂ] L2d 3} {G₂ : Dom₂ →ₗ[ℂ] L2d 3}
    (h₁ : IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G₁)
    (h₂ : IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G₂) :
    Dom₁ = Dom₂ ∧ ∀ (x : L2d 3) (h : x ∈ Dom₁) (h' : x ∈ Dom₂), G₁ ⟨x, h⟩ = G₂ ⟨x, h'⟩ := by
  exact isSelfAdjointExtension_unique_of_esa (BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine A c) h₁ h₂
#print axioms solution
