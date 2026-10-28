-- Prove2me | solution 1 for D1Bound5.bennettChoose_ne_zero_of_avoids_naturals
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:26:09.61898+00:00
-- url     : https://prove2.me/submissions/f787d6a3-c450-4f44-b9c8-db76af3e710b

import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination

section
open Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- A generalized binomial coefficient is nonzero whenever its upper
parameter avoids the first k natural numbers. -/
theorem _root_.solution (r : F) (k : ℕ)
    (h : ∀ j : ℕ, j < k → r ≠ (j : F)) : Ring.choose r k ≠ 0 := by
  have hpoch : (descPochhammer F k).eval r ≠ 0 := by
    rw [descPochhammer_eval_eq_prod_range]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (h j (Finset.mem_range.mp hj))
  have heq : (descPochhammer ℤ k).smeval r = (descPochhammer F k).eval r := by
    rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
      descPochhammer_eval_eq_ascPochhammer]
  intro hz
  have hh := Ring.descPochhammer_eq_factorial_smul_choose r k
  rw [heq, hz, smul_zero] at hh
  exact hpoch hh





end D1Bound5
end
