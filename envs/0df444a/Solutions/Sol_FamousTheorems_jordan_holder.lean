-- Prove2me | solution 1 for FamousTheorems.jordan_holder
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:16:01.114814+00:00
-- url     : https://prove2.me/submissions/ce2e07e4-5413-492c-b88d-c1cce4af5863

import Mathlib

theorem solution {X : Type*} [Lattice X] [JordanHolderLattice X] (s₁ s₂ : CompositionSeries X)
    (hb : RelSeries.head s₁ = RelSeries.head s₂) (ht : RelSeries.last s₁ = RelSeries.last s₂) :
    s₁.Equivalent s₂ :=
  CompositionSeries.jordan_holder s₁ s₂ hb ht
