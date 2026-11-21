-- Prove2me | solution 1 for ExactDFTRefine.Main.appendix_a
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:46:48.534938+00:00
-- url     : https://prove2.me/submissions/fe9909af-bf83-41e6-b10a-a23925476928

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Appendix A**, p. 8. For `N ≥ 1` and `0 ≤ x ≤ 1`: `S_N(x) ≤ e^x ≤ U_N(x)`, where
`S_N(x) = ∑_{j=0}^{N-1} x^j/j!` and `U_N(x) = S_N(x) + ((N + 1)/(N N!)) x^N`. -/
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    SN N x ≤ Real.exp x ∧ Real.exp x ≤ UN N x := by
  constructor
  · exact Real.sum_le_exp_of_nonneg hx0 N
  · have h := Real.exp_bound' hx0 hx1 (n := N) (by omega)
    have hfac : (N.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero N
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    calc Real.exp x
        ≤ (∑ j ∈ Finset.range N, x ^ j / (j.factorial : ℝ)) +
            x ^ N * ((N : ℝ) + 1) / ((N.factorial : ℝ) * (N : ℝ)) := h
      _ = UN N x := by
        unfold UN SN
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring

end ExactDFTRefine.Main
