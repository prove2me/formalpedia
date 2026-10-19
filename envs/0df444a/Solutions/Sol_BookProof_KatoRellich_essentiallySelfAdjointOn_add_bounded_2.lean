-- Prove2me | solution 2 for BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:33:37.94337+00:00
-- url     : https://prove2.me/submissions/5eea2934-d397-48e0-8f9a-05bbd4ec9d1d

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded_prime
-- Generated from ChapterKatoRellichDeficiency.lean — theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}


theorem solution [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype)) := by
  exact BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded_prime H hH hesa B hB

