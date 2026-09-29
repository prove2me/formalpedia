-- Prove2me | solution 1 for FamousTheorems.matroid_bases_equal_card_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:39:37.541126+00:00
-- url     : https://prove2.me/submissions/f00664d8-c0ca-450f-8bc2-f74004f78cd0

import Mathlib

theorem solution {α : Type*} {M : Matroid α} {B₁ B₂ : Set α} (h₁ : M.IsBase B₁) (h₂ : M.IsBase B₂) :
    B₁.encard = B₂.encard :=
  h₁.encard_eq_encard_of_isBase h₂
