-- Prove2me | solution 1 for Finset.sum_addConvolution_eq_card_product
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:45.830492+00:00
-- url     : https://prove2.me/submissions/76efcf23-95a8-468b-83fe-6593ead64d64

import Mathlib

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card := by
  simp_rw [Finset.addConvolution]
  rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_eq_self.mpr,
    Finset.card_product]
  rintro ⟨a, b⟩ hab
  rw [Finset.mem_product] at hab
  exact Finset.add_mem_add hab.1 hab.2
