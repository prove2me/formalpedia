-- Prove2me | solution 1 for DiazModulus.log_two_log_three_not_both_rational
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T06:28:46.0542+00:00
-- url     : https://prove2.me/submissions/c20455c1-9d0d-4873-b5f9-cec15602da29

import Mathlib
import Theorems.Thm_DiazModulus_torsion_rational_modulus_unique

/-!
# `(log 2)² + π²` and `(log 3)² + π²` are not both rational

`e^{log 2} = 2` and `e^{log 3} = 3` are algebraic. If both squared moduli were rational, the
uniqueness of the torsion pair at a rational squared modulus would give `log 3 = ± log 2`. Both
logarithms are positive and `log 2 < log 3`, so neither sign is possible.
-/

namespace R1_log_two_log_three_not_both_rational

/-- `e^{log n} = n` is algebraic for every positive natural number `n`. -/
theorem isAlgebraic_exp_log_natCast (n : ℕ) (hn : 0 < n) :
    IsAlgebraic ℚ (Complex.exp ((Real.log n : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log (Nat.cast_pos.mpr hn), Complex.ofReal_natCast]
  exact isAlgebraic_natCast n

end R1_log_two_log_three_not_both_rational

open R1_log_two_log_three_not_both_rational in
theorem solution :
    ¬ ∃ r s : ℚ, Real.log 2 ^ 2 + Real.pi ^ 2 = r ∧ Real.log 3 ^ 2 + Real.pi ^ 2 = s := by
  rintro ⟨r, s, hr, hs⟩
  have h2 := isAlgebraic_exp_log_natCast 2 (by norm_num)
  have h3 := isAlgebraic_exp_log_natCast 3 (by norm_num)
  push_cast at h2 h3
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases DiazModulus.torsion_rational_modulus_unique (Real.log 2) (Real.log 3) h2 h3 r s hr hs
    with h | h <;> linarith
