-- Prove2me | solution 1 for FCP.AgohGiuga.agoh_giuga_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T21:18:43.791586+00:00
-- url     : https://prove2.me/submissions/88886078-16fb-43ed-9032-98926863327c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FCP_AgohGiuga_giuga_criterion
import Theorems.Thm_FCP_AgohGiuga_giuga_conjecture_arith

open FCP.AgohGiuga

theorem solution (p : ℕ) (hp : 2 ≤ p) :
    p.Prime ↔ p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i ^ (p - 1) := by
  constructor
  · intro hprime
    refine (giuga_criterion p hp).mpr ?_
    intro q hq hqp
    have hq_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq hprime).mp hqp
    subst hq_eq
    simp [Nat.div_self hq.pos]
  · intro hdvd
    exact giuga_conjecture_arith p hp ((giuga_criterion p hp).mp hdvd)
