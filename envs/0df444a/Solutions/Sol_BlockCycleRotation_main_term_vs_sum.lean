-- Prove2me | solution 1 for BlockCycleRotation.main_term_vs_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:26:55.304387+00:00
-- url     : https://prove2.me/submissions/5d2c0798-eddf-4a20-bef9-3950c9d33099

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The rounding term, in the paper's form.**

The paper compares the closed form at the *real* bound `V` — namely
`A·V + B·V²/2` — with the actual sum `∑_{1 ≤ b' < V} (A + B·b')`, and bounds the
difference by `|A| + |B·V|`.  Writing `K` for the largest admissible `b'`, so
that `K ≤ V < K+1` and the sum is `A·K + B·K(K+1)/2`, that is what is proved
here. -/
theorem solution (A B V : ℝ) (K : ℕ) (hK : (K : ℝ) ≤ V) (hK1 : V ≤ (K : ℝ) + 1)
    (hV : 1 ≤ V) :
    |(A * V + B * V ^ 2 / 2) - (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)|
      ≤ |A| + |B| * V:= by
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hdiff : (A * V + B * V ^ 2 / 2) - (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      = A * (V - (K : ℝ)) + B / 2 * (V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ)) := by ring
  rw [hdiff]
  have h1 : |V - (K : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : |V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ)| ≤ 2 * V := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |A * (V - (K : ℝ)) + B / 2 * (V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ))|
      ≤ |A * (V - (K : ℝ))| + |B / 2 * (V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ))| := abs_add_le _ _
    _ = |A| * |V - (K : ℝ)| + |B| / 2 * |V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ)| := by
        rw [abs_mul, abs_mul, abs_div, abs_two]
    _ ≤ |A| * 1 + |B| / 2 * (2 * V) := by
        have ha := abs_nonneg A
        have hb : (0 : ℝ) ≤ |B| / 2 := by positivity
        nlinarith
    _ = |A| + |B| * V := by ring
