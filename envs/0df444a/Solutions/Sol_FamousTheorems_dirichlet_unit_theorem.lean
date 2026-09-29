-- Prove2me | solution 1 for FamousTheorems.dirichlet_unit_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:06:28.312497+00:00
-- url     : https://prove2.me/submissions/5f400429-5cba-4af7-9962-a814c2955244

import Mathlib

theorem solution (K : Type*) [Field K] [NumberField K] :
    ∃ u : Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ, ∀ x : (NumberField.RingOfIntegers K)ˣ,
      ∃! ζe : NumberField.Units.torsion K × (Fin (NumberField.Units.rank K) → ℤ),
        x = (ζe.1 : (NumberField.RingOfIntegers K)ˣ) * ∏ i, u i ^ ζe.2 i :=
  ⟨NumberField.Units.fundSystem K, NumberField.Units.exist_unique_eq_mul_prod K⟩
