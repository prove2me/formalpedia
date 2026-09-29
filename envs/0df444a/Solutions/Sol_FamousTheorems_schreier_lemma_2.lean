-- Prove2me | solution 2 for FamousTheorems.schreier_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:34:17.753711+00:00
-- url     : https://prove2.me/submissions/9f7084d4-6d00-4228-990d-38dfafe560de

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [Group G] {H : Subgroup G} {R S : Set G} (hR : Subgroup.IsComplement (H : Set G) R)
    (hR1 : (1 : G) ∈ R) (hS : Subgroup.closure S = ⊤) :
    Subgroup.closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) = H :=
  Subgroup.closure_mul_image_eq hR hR1 hS
