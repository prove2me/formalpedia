-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.submodular_minimizer_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:45:04.175604+00:00
-- url     : https://prove2.me/submissions/9fcd2401-a519-4faf-8bdb-e0edef88251a

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_Submodular

open Classical in
open scoped Pointwise in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (rho : Finset V → WithTop ℝ)
    (hrho : DiscreteConvex.LConvexFunctionsB.Submodular rho)
    (X : Finset V) (hX : rho X ≠ ⊤) :
    (∀ Y : Finset V, rho X ≤ rho Y) ↔
      (∀ Y : Finset V, (X ⊆ Y ∨ Y ⊆ X) → rho X ≤ rho Y) := by
  constructor
  · intro h Y _
    exact h Y
  · intro h Y
    have h1 : rho X ≤ rho (X ∪ Y) := h _ (Or.inl Finset.subset_union_left)
    have h2 : rho X ≤ rho (X ∩ Y) := h _ (Or.inr Finset.inter_subset_left)
    have hs := hrho X Y
    have h3 : rho X + rho X ≤ rho X + rho Y :=
      le_trans (add_le_add h1 h2) hs
    exact (WithTop.add_le_add_iff_left hX).1 h3
