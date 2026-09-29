-- Prove2me | solution 1 for FamousTheorems.five_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:43.374389+00:00
-- url     : https://prove2.me/submissions/92f6908c-bb6f-4d75-b354-45889643e1ed

import Mathlib

theorem solution {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C] {R₁ R₂ : CategoryTheory.ComposableArrows C 4}
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (φ : R₁ ⟶ R₂)
    (h₀ : CategoryTheory.Epi (CategoryTheory.ComposableArrows.app' φ 0))
    (h₁ : CategoryTheory.IsIso (CategoryTheory.ComposableArrows.app' φ 1))
    (h₃ : CategoryTheory.IsIso (CategoryTheory.ComposableArrows.app' φ 3))
    (h₄ : CategoryTheory.Mono (CategoryTheory.ComposableArrows.app' φ 4)) :
    CategoryTheory.IsIso (CategoryTheory.ComposableArrows.app' φ 2) :=
  CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ φ h₀ h₁ h₃ h₄
