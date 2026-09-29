-- Prove2me | solution 1 for FamousTheorems.glaisher
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:16:58.172982+00:00
-- url     : https://prove2.me/submissions/e5a7c026-4a2c-4409-bc50-4342dc95c124

import Mathlib

theorem solution (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (Nat.Partition.restricted n fun x => ¬ m ∣ x).card = (Nat.Partition.countRestricted n m).card :=
  Nat.Partition.card_restricted_eq_card_countRestricted n hm
