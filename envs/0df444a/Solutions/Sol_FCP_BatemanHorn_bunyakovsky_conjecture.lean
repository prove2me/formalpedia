-- Prove2me | solution 1 for FCP.BatemanHorn.bunyakovsky_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:01:11.135672+00:00
-- url     : https://prove2.me/submissions/191a2e71-a94c-4065-b279-0df138c285b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FCP_BatemanHorn
import Theorems.Thm_FCP_BatemanHorn_bunyakovsky_linear
import Theorems.Thm_FCP_BatemanHorn_bunyakovsky_degree_ge_two

open Polynomial FCP.BatemanHorn

theorem solution (f : ℤ[X]) (h_bunyakovsky : BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition {f}) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by
  -- The Bunyakovsky condition gives degree ≥ 1; split into degree = 1 and degree ≥ 2.
  rcases Nat.lt_or_ge f.natDegree 2 with h | h
  · -- degree exactly one: Dirichlet's theorem on primes in arithmetic progressions
    have h1 : f.natDegree = 1 := le_antisymm (Nat.lt_succ_iff.mp h) h_bunyakovsky.2.1
    exact bunyakovsky_linear f h_bunyakovsky h1
  · -- degree at least two: the genuinely open part
    exact bunyakovsky_degree_ge_two f h_bunyakovsky h_schinzel h
