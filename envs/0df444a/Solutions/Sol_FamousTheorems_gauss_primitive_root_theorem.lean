-- Prove2me | solution 1 for FamousTheorems.gauss_primitive_root_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:06:22.69972+00:00
-- url     : https://prove2.me/submissions/f4e2372a-9ae6-47b9-8688-897516efe827

import Mathlib

theorem solution (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p m : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) :=
  ZMod.isCyclic_units_iff n
