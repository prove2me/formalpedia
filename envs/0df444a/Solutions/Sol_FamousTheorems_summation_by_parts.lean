-- Prove2me | solution 1 for FamousTheorems.summation_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:24:47.611222+00:00
-- url     : https://prove2.me/submissions/f665f1cd-a3c5-4622-960e-dc7213a3e25d

import Mathlib

theorem solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}
    (hmn : m < n) :
    ∑ i ∈ Finset.Ico m n, f i • g i =
      f (n - 1) • ∑ i ∈ Finset.range n, g i - f m • ∑ i ∈ Finset.range m, g i -
        ∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j :=
  Finset.sum_Ico_by_parts f g hmn
