-- Prove2me | solution 1 for DirichletUnitTheorem.dirichlet_unit_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:29:09.167033+00:00
-- url     : https://prove2.me/submissions/0292226c-91c3-41fa-80b2-b9a0f1127ef8

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K] :
    Group.FG (𝓞 K)ˣ ∧
      Module.rank ℤ (Additive (𝓞 K)ˣ) =
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : Cardinal) := by
  refine ⟨Group.fg_iff_monoid_fg.mpr inferInstance, ?_⟩
  rw [← Module.finrank_eq_rank, Units.finrank_eq, Units.rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
