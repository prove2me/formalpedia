-- Prove2me | solution 1 for FamousTheorems.kummer_theorem_binomial
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:59.75438+00:00
-- url     : https://prove2.me/submissions/04f6a5e2-0171-47c4-ac24-087f55963556

import Mathlib

theorem solution {p n k b : ℕ} [Fact p.Prime] (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) =
      ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  padicValNat_choose hkn hnb
