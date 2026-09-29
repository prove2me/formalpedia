-- Prove2me | solution 1 for FamousTheorems.schreier_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:33:22.352288+00:00
-- url     : https://prove2.me/submissions/8d19dc5d-0c34-4e01-9a6a-e437a5972893

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [Group G] {H : Subgroup G} {R S : Set G} (hR : Subgroup.IsComplement (H : Set G) R)
    (hR1 : (1 : G) ∈ R) (hS : Subgroup.closure S = ⊤) :
    Subgroup.closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) = H :=
  Subgroup.closure_mul_image_eq hR hR1 hS
