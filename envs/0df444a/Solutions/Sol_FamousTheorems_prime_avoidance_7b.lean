-- Prove2me | solution 1 for FamousTheorems.prime_avoidance_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:55:56.398771+00:00
-- url     : https://prove2.me/submissions/3dc8d47c-a2e4-4dbf-94cd-f72b2e0174a5

import Mathlib

theorem solution {ι R : Type*} [CommRing R] {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ (s : Set ι), (f i : Set R)) ↔ ∃ i ∈ s, I ≤ f i :=
  Ideal.subset_union_prime a b hp
