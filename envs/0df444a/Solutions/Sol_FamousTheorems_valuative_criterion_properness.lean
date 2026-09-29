-- Prove2me | solution 1 for FamousTheorems.valuative_criterion_properness
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:59:06.330981+00:00
-- url     : https://prove2.me/submissions/9915abb9-6f81-4f7b-97c0-5d49bd1f2377

import Mathlib

open AlgebraicGeometry

theorem solution {X Y : Scheme} (f : X ⟶ Y) :
    IsProper f ↔ ValuativeCriterion f ∧ QuasiCompact f ∧ QuasiSeparated f ∧ LocallyOfFiniteType f :=
  by
    rw [IsProper.eq_valuativeCriterion]
    exact ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩⟩
