-- Prove2me | solution 2 for FamousTheorems.ping_pong_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:36:55.680684+00:00
-- url     : https://prove2.me/submissions/58145ba9-f0ca-42d9-927e-7afe41a190c2

import Mathlib

open Pointwise

theorem solution {ι G : Type*} [Group G] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (hcard : 3 ≤ Cardinal.mk ι ∨ ∃ i, 3 ≤ Cardinal.mk (H i)) {α : Type*} [MulAction G α] (X : ι → Set α)
    (hXne : ∀ i, (X i).Nonempty) (hXdisj : Pairwise (Function.onFun Disjoint X))
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i) [Nontrivial ι] :
    Function.Injective (Monoid.CoprodI.lift f) := by
  exact Monoid.CoprodI.lift_injective_of_ping_pong f hcard X hXne hXdisj hpp
