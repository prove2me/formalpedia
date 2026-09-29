-- Prove2me | solution 1 for FamousTheorems.partial_fraction_decomposition_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:16:27.895843+00:00
-- url     : https://prove2.me/submissions/ac3795b2-e9e0-4b7f-8209-e58c9772af49

import Mathlib

open scoped algebraMap

theorem solution {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra (Polynomial R) K] [FaithfulSMul (Polynomial R) K]
    (f : Polynomial R) {ι : Type*} {g : ι → Polynomial R} {s : Finset ι} (hg : ∀ i ∈ s, (g i).Monic)
    (hcop : Set.Pairwise (s : Set ι) fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : Polynomial R) (r : ι → Polynomial R), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      (f : K) / ∏ i ∈ s, (g i : K) = (q : K) + ∑ i ∈ s, (r i : K) / (g i : K) :=
  Polynomial.div_prod_eq_quo_add_sum_rem_div K f hg hcop
