-- Prove2me | solution 1 for FamousTheorems.faa_di_bruno
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:22.955613+00:00
-- url     : https://prove2.me/submissions/27b25c69-018a-49da-813a-a4b7b7eafaa4

import Mathlib

theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] {g f : 𝕜 → 𝕜} {x : 𝕜} {n : WithTop ℕ∞} {i : ℕ}
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        iteratedDeriv c.length g (f x) * ∏ j : Fin c.length, iteratedDeriv (c.partSize j) f x :=
  iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf hi
