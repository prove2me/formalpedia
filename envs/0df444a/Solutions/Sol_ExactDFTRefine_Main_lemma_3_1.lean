-- Prove2me | solution 1 for ExactDFTRefine.Main.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:47:55.913181+00:00
-- url     : https://prove2.me/submissions/fb05aedb-f40c-4a40-8cd3-31c9787a0db2

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Lemma 3.1**, p. 3. With `S_6(x) = ∑_{j=0}^{5} x^j/j!`: `S_6(x) ≤ e^x` for `x ≥ 0`, and
`e^x ≤ S_6(x) + (7/4320) x^6` for `0 ≤ x ≤ 1` (Eq. (4)). -/
theorem lemma_3_1 :
    (∀ x : ℝ, 0 ≤ x → SN 6 x ≤ Real.exp x) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.exp x ≤ SN 6 x + 7 / 4320 * x ^ 6) := by
  constructor
  · intro x hx
    exact Real.sum_le_exp_of_nonneg hx 6
  · intro x hx0 hx1
    have h := Real.exp_bound' hx0 hx1 (n := 6) (by decide)
    calc Real.exp x
        ≤ ∑ j ∈ Finset.range 6, x ^ j / (j.factorial : ℝ) +
            x ^ 6 * (6 + 1) / ((Nat.factorial 6 : ℝ) * 6) := h
      _ = SN 6 x + 7 / 4320 * x ^ 6 := by
          unfold SN
          norm_num [Nat.factorial]
          ring

end ExactDFTRefine.Main

open ExactDFTRefine.Main

theorem solution :
    (∀ x : ℝ, 0 ≤ x → SN 6 x ≤ Real.exp x) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.exp x ≤ SN 6 x + 7 / 4320 * x ^ 6) :=
  lemma_3_1
