-- Prove2me | solution 1 for FamousTheorems.complete_ordered_field_unique_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:19:49.364337+00:00
-- url     : https://prove2.me/submissions/8e9b82f2-0442-43ee-90c2-29f6a21fc54c

import Mathlib

theorem solution (β γ : Type*) [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
    [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ] : Nonempty (Unique (β ≃+*o γ)) :=
  ⟨ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso β γ⟩
