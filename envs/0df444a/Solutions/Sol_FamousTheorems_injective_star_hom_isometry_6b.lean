-- Prove2me | solution 1 for FamousTheorems.injective_star_hom_isometry_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:42:31.92745+00:00
-- url     : https://prove2.me/submissions/f573b0a4-2c6b-461f-a49c-1cddfe081886

import Mathlib

theorem solution {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : Function.Injective φ) : Isometry φ :=
  NonUnitalStarAlgHom.isometry φ hφ
