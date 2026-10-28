-- Prove2me | solution 1 for D1Bound5.finiteHomogeneousTwo_norm_le_ratio
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:05.039681+00:00
-- url     : https://prove2.me/submissions/70ef0e2e-fd80-48c0-ab3a-5e8418abf74b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
noncomputable section

namespace D1Bound5





/-- Retain the exact first-anchor ratio in each actual homogeneous
coefficient polynomial, instead of replacing both anchor moduli by B. -/
theorem _root_.solution (n : ℕ) (v : Fin (n+1) → ℤ)
    (x y : ℂ) (r : ℝ) (hr : 0 ≤ r) (hxy : ‖x‖ ≤ r*‖y‖) :
    ‖finiteHomogeneousTwo n v x y‖ ≤ finiteHomogeneousRatioWeight n v r*‖y‖^n := by
  unfold finiteHomogeneousTwo
  calc
    _ ≤ ∑ j, ‖(v j : ℂ)*x^(j : ℕ)*y^(n-(j : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ j, |(v j : ℝ)| *r^(j : ℕ)*‖y‖^n := by
      apply Finset.sum_le_sum
      intro j _
      have hj : (j : ℕ) ≤ n := by omega
      have hsum : (j : ℕ)+(n-(j : ℕ)) = n := by omega
      have hnorm : ‖(v j : ℂ)‖ = |(v j : ℝ)| := by simp
      rw [norm_mul,norm_mul,norm_pow,norm_pow,hnorm]
      calc
        _ ≤ |(v j : ℝ)| *(r*‖y‖)^(j : ℕ)*‖y‖^(n-(j : ℕ)) := by gcongr
        _ = _ := by rw [mul_pow]; rw [mul_assoc,mul_assoc,← pow_add,hsum]; ring
    _ = _ := by simp only [finiteHomogeneousRatioWeight, Finset.sum_mul]







end D1Bound5
end
