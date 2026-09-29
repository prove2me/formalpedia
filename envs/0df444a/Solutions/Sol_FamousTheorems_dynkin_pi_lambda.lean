-- Prove2me | solution 1 for FamousTheorems.dynkin_pi_lambda
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:10:05.354646+00:00
-- url     : https://prove2.me/submissions/a97f3051-9bb1-4a62-964e-ea24a3a2c134

import Mathlib

theorem solution {α : Type*} {m : MeasurableSpace α} {C : Set α → Prop} {s : Set (Set α)}
    (h_eq : m = MeasurableSpace.generateFrom s) (h_inter : IsPiSystem s) (h_empty : C ∅)
    (h_basic : ∀ t ∈ s, C t) (h_compl : ∀ t, MeasurableSet t → C t → C tᶜ)
    (h_union : ∀ f : ℕ → Set α, Pairwise (Function.onFun Disjoint f) → (∀ i, MeasurableSet (f i)) →
      (∀ i, C (f i)) → C (⋃ i, f i)) :
    ∀ t, MeasurableSet t → C t :=
  fun t ht => MeasurableSpace.induction_on_inter (C := fun t _ => C t) h_eq h_inter h_empty h_basic h_compl h_union t ht
