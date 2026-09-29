-- Prove2me | solution 1 for FamousTheorems.prime_ideal_theorem_distributive_lattice
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:13:36.333732+00:00
-- url     : https://prove2.me/submissions/7381b5e6-5504-4db9-8218-ef89931a786e

import Mathlib

theorem solution {α : Type*} [DistribLattice α] {F : Order.PFilter α} {I : Order.Ideal α}
    (h : Disjoint (F : Set α) (I : Set α)) :
    ∃ J : Order.Ideal α, J.IsPrime ∧ I ≤ J ∧ Disjoint (F : Set α) (J : Set α) :=
  DistribLattice.prime_ideal_of_disjoint_filter_ideal h
