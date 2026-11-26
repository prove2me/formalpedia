-- Prove2me | solution 1 for FirstPassageLinearTransport.landingBad_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:18:02.623597+00:00
-- url     : https://prove2.me/submissions/08fb8b17-f742-4117-a61c-8752553bdf79

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Theorems.Thm_FirstPassageLinearTransport_one_div_two_pow_eq_exp

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {q : ℕ} (hq : 1 ≤ q) {t b : ℝ}
    (hcard : ((landingBad q t).card : ℝ) ≤
      1 + (2 : ℝ) ^ q *
        Real.exp (-(((q - 1 : ℕ) : ℝ) * b))) :
    ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q ≤
      Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))) := by
  have hpow : 0 < (2 : ℝ) ^ q := by positivity
  have hdiv := (div_le_div_iff_of_pos_right hpow).2 hcard
  rw [add_div, mul_div_cancel_left₀ _ hpow.ne'] at hdiv
  rw [one_div_two_pow_eq_exp] at hdiv
  calc
    ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q ≤
        Real.exp (-(Real.log 2 * (q : ℝ))) +
          Real.exp (-(((q - 1 : ℕ) : ℝ) * b)) := hdiv
    _ = Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))) := by
      rw [← Real.exp_add]
      congr 2
      rw [Nat.cast_sub hq]
      push_cast
      ring
end FirstPassageLinearTransport
