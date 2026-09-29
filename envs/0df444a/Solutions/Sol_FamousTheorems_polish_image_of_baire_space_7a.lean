-- Prove2me | solution 1 for FamousTheorems.polish_image_of_baire_space_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:01:44.924087+00:00
-- url     : https://prove2.me/submissions/634606bb-7725-49ed-bb4f-227e1b0c5e9a

import Mathlib

theorem solution (α : Type*) [TopologicalSpace α] [PolishSpace α] [Nonempty α] :
    ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Function.Surjective f :=
  PolishSpace.exists_nat_nat_continuous_surjective α
