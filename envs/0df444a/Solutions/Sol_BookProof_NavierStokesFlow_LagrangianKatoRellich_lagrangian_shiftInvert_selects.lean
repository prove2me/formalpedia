-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_shiftInvert_selects
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-15T12:50:26.250431+00:00
-- url     : https://prove2.me/submissions/9bbe5143-0ddf-43bf-9568-3db69804763c

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_shiftInvert_selects
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lagrangian_selfAdjoint_extension
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterHashimotoComplexShifts
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_dom_eq_range
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_opNorm_le
import Theorems.Thm_BookProof_HashimotoShiftInvert_exists_isShiftInvertC
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_determines
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L)) {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : F →L[ℂ] F),
      IsSelfAdjointExtension (lagrangianCore L) A ∧ IsShiftInvertC A γ X ∧
      ‖X‖ ≤ |γ.im|⁻¹ ∧ Dom = LinearMap.range ((X : F →ₗ[ℂ] F)) ∧
      (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvertC A' γ X →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by

  obtain ⟨Dom, A, hA⟩ := lagrangian_selfAdjoint_extension L hesa
  obtain ⟨hext, hsym, hsa⟩ := hA
  obtain ⟨X, hX⟩ := exists_isShiftInvertC hsym hγ (cshiftMap_surjective hsym hsa hγ)
  refine ⟨Dom, A, X, ⟨hext, hsym, hsa⟩, hX, hX.opNorm_le hsym hγ, hX.dom_eq_range, ?_⟩
  intro Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvertC_determines hA' hX
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩
