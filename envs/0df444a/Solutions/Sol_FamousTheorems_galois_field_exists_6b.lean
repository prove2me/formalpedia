-- Prove2me | solution 1 for FamousTheorems.galois_field_exists_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:14:28.982272+00:00
-- url     : https://prove2.me/submissions/4a15922f-026a-48b8-a56a-8a3b6730c7ba

import Mathlib

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) : ∃ (K : Type) (_ : Field K), Nat.card K = p ^ n :=
  ⟨GaloisField p n, inferInstance, GaloisField.card p n hn⟩
