-- Prove2me | solution 1 for FamousTheorems.lefschetz_principle_acf
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:08:02.307997+00:00
-- url     : https://prove2.me/submissions/1f9c8599-4750-4ec8-a534-c188657bfb9b

import Mathlib

theorem solution {φ : FirstOrder.Language.ring.Sentence} :
    FirstOrder.Language.Theory.ACF 0 ⊨ᵇ φ ↔
      {p : Nat.Primes | FirstOrder.Language.Theory.ACF (p : ℕ) ⊨ᵇ φ}.Infinite :=
  FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize
