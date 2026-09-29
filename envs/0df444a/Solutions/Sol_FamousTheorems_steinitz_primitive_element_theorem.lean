-- Prove2me | solution 1 for FamousTheorems.steinitz_primitive_element_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:51:43.216306+00:00
-- url     : https://prove2.me/submissions/99f35485-9c50-41ca-b1b6-b753003efaf4

import Mathlib

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E] :
    (Algebra.IsAlgebraic F E ∧ ∃ α : E, IntermediateField.adjoin F {α} = ⊤) ↔ Finite (IntermediateField F E) :=
  Field.exists_primitive_element_iff_finite_intermediateField F E
