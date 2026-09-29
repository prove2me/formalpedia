-- Prove2me | solution 1 for FamousTheorems.fine_wilf_periodicity_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:17:04.391983+00:00
-- url     : https://prove2.me/submissions/02add607-4c6b-4f0b-8e06-9cee36ac599f

import Mathlib

theorem solution {α : Type*} {w : List α} {p q : ℕ} (hp : w.HasPeriod p) (hq : w.HasPeriod q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) :
    w.HasPeriod (Nat.gcd p q) :=
  hp.gcd hq hlen
