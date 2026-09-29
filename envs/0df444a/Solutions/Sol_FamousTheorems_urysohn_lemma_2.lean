-- Prove2me | solution 2 for FamousTheorems.urysohn_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:37:48.692285+00:00
-- url     : https://prove2.me/submissions/465ca157-765d-4bf4-8727-61af32e9a098

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : ∃ f : C(X, ℝ), Set.EqOn f 0 s ∧ Set.EqOn f 1 t ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isClosed hs ht hd
