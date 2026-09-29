-- Prove2me | solution 1 for FamousTheorems.primitive_element_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:13:11.966144+00:00
-- url     : https://prove2.me/submissions/4dd782e6-4956-4081-aba9-b31d23901901

import Mathlib

open IntermediateField

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ α : E, F⟮α⟯ = ⊤ :=
  Field.exists_primitive_element F E
