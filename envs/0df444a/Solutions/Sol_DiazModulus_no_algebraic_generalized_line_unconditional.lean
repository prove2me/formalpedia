-- Prove2me | solution 1 for DiazModulus.no_algebraic_generalized_line_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T11:29:41.636991+00:00
-- url     : https://prove2.me/submissions/b090c529-1fc6-4c1d-9ea8-f5fc15b2c2f2

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_no_algebraic_generalized_line
import Theorems.Thm_DiazModulus_baker_two_logs

/-- `no_algebraic_generalized_line` with its Baker antecedent discharged by `baker_two_logs`, whose
statement is exactly that antecedent. -/
theorem solution :
    ∀ l : ℂ, IsAlgebraic ℚ (Complex.exp l) → l.re ≠ 0 → l.im ≠ 0 →
      ∀ B C : ℂ, IsAlgebraic ℚ B → B ≠ 0 → IsAlgebraic ℚ C →
        B * l + (starRingEnd ℂ) B * (starRingEnd ℂ) l + C ≠ 0 := by
  exact DiazModulus.no_algebraic_generalized_line DiazModulus.baker_two_logs

#print axioms solution
