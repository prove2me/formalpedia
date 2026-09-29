-- Prove2me | solution 1 for FamousTheorems.cauchy_davenport_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:52:18.639974+00:00
-- url     : https://prove2.me/submissions/29d411da-720f-4215-a37e-d9d8569d8f85

import Mathlib

open scoped Pointwise

theorem solution {p : ℕ} (hp : p.Prime) {s t : Finset (ZMod p)} (hs : s.Nonempty) (ht : t.Nonempty) :
    min p (s.card + t.card - 1) ≤ (s + t).card := by
  exact ZMod.cauchy_davenport hp hs ht
