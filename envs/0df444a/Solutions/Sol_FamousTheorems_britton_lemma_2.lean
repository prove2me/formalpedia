-- Prove2me | solution 2 for FamousTheorems.britton_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:36:44.646527+00:00
-- url     : https://prove2.me/submissions/856b3328-0daf-49b8-8094-83b03ac8c537

import Mathlib

theorem solution {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B) (w : HNNExtension.NormalWord.ReducedWord G A B)
    (hw : HNNExtension.NormalWord.ReducedWord.prod φ w ∈ (HNNExtension.of : G →* HNNExtension G A B φ).range) :
    w.toList = [] := by
  exact HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ w hw
