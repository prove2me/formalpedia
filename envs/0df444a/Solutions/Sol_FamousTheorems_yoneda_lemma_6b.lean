-- Prove2me | solution 1 for FamousTheorems.yoneda_lemma_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:24:09.564978+00:00
-- url     : https://prove2.me/submissions/cd2001df-86aa-474b-abea-e467d7440a91

import Mathlib

open CategoryTheory Opposite

theorem solution {C : Type*} [Category C] (X : C) (F : Cᵒᵖ ⥤ Type _) :
    Nonempty ((yoneda.obj X ⟶ F) ≃ F.obj (op X)) :=
  ⟨yonedaEquiv⟩
