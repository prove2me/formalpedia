-- Prove2me | solution 1 for BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:41:11.138531+00:00
-- url     : https://prove2.me/submissions/918d791c-95e8-4a2e-84a3-55140f572764

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clExt_isClosureOf
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_of_farisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hdense : Dense (D : Set F)) (hH : SymmetricOn D H) (hN : SymmetricOn D N) (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    IsClosureOf H (clExt H hdense hH) ∧ IsSelfAdjointExtension H (clExt H hdense hH) ∧
      ∀ {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F), IsSelfAdjointExtension H A →
        Dom = clDom H ∧ ∀ (x : F) (h : x ∈ Dom) (h' : x ∈ clDom H),
          A ⟨x, h⟩ = clExt H hdense hH ⟨x, h'⟩ := by

  have hesa : EssentiallySelfAdjointOn D H :=
    essentiallySelfAdjointOn_of_farisLavine H N c hH hN hc hNpos hNsurj hcomm
  have hSA : IsSelfAdjointExtension H (clExt H hdense hH) :=
    ⟨fun v => ⟨coe_mem_clDom H v, clExt_extends H hdense hH v⟩,
      clExt_symmetricOn H hdense hH,
      clExt_selfAdjointCriterion H hdense hH hesa⟩
  exact ⟨clExt_isClosureOf H hdense hH, hSA,
    fun A hA => isSelfAdjointExtension_unique_of_esa hesa hA hSA⟩
