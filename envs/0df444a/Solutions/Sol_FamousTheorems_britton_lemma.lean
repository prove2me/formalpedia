-- Prove2me | solution 1 for FamousTheorems.britton_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:35:29.099109+00:00
-- url     : https://prove2.me/submissions/72045cce-342c-48c5-b6be-670443b4744f

import Mathlib

theorem solution {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B) (w : HNNExtension.NormalWord.ReducedWord G A B)
    (hw : HNNExtension.NormalWord.ReducedWord.prod φ w ∈ (HNNExtension.of : G →* HNNExtension G A B φ).range) :
    w.toList = [] :=
  HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ w hw
