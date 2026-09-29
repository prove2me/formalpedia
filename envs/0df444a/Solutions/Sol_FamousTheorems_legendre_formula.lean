-- Prove2me | solution 1 for FamousTheorems.legendre_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:13:00.042301+00:00
-- url     : https://prove2.me/submissions/ef9b3a68-f7c3-499c-a4ff-fd946f00a42b

import Mathlib

theorem solution {p n b : ℕ} [Fact p.Prime] (hnb : Nat.log p n < b) :
    padicValNat p n.factorial = ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
  padicValNat_factorial hnb
