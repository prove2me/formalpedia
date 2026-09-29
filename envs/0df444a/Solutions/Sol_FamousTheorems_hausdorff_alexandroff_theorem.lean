-- Prove2me | solution 1 for FamousTheorems.hausdorff_alexandroff_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:21:37.319339+00:00
-- url     : https://prove2.me/submissions/b4696798-debe-4e73-8006-83dbbb9c9a65

import Mathlib

theorem solution (X : Type*) [Nonempty X] [MetricSpace X] [CompactSpace X] :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Surjective f :=
  exists_nat_bool_continuous_surjective_of_compact X
