-- Prove2me | solution 1 for ChenWhitt93.Reflection.neumann_inverse_identity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T14:42:42.052262+00:00
-- url     : https://prove2.me/submissions/182760b1-52be-4a3c-b9d0-bd5336915a46

import Mathlib

open Filter Topology Matrix

theorem solution {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (hsum : Summable (fun k : Nat => Q ^ k)) :
    (tsum fun k : Nat => Q ^ k) * (1 - Q) = 1 ∧
      (1 - Q) * (tsum fun k : Nat => Q ^ k) = 1 := by
  exact ⟨hsum.tsum_pow_mul_one_sub, hsum.one_sub_mul_tsum_pow⟩
