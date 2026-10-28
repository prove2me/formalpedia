-- Prove2me | solution 1 for D1Bound5.finiteHomogeneousTwo_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:47.813058+00:00
-- url     : https://prove2.me/submissions/c6cf81d2-1fbe-4f3c-869a-e4594903d58c

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
namespace D1Bound5



/-- The usual coefficient sum bounds the actual homogeneous polynomial.
No coefficient or polynomial-height certificate is assumed. -/
theorem _root_.solution (n : ℕ) (v : Fin (n+1) → ℤ)
    (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖) :
    ‖finiteHomogeneousTwo n v x y‖ ≤
      (∑ j, |(v j : ℝ)|)*‖y‖^n := by
  unfold finiteHomogeneousTwo
  calc
    _ ≤ ∑ j, ‖(v j : ℂ)*x^(j : ℕ)*y^(n-(j : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ j, |(v j : ℝ)| *‖y‖^n := by
      apply Finset.sum_le_sum
      intro j _
      have hj : (j : ℕ) ≤ n := by omega
      have hsum : (j : ℕ)+(n-(j : ℕ)) = n := by omega
      have hnorm : ‖(v j : ℂ)‖ = |(v j : ℝ)| := by simp
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hnorm]
      calc
        _ ≤ |(v j : ℝ)| *‖y‖^(j : ℕ)*‖y‖^(n-(j : ℕ)) := by gcongr
        _ = _ := by rw [mul_assoc, ← pow_add, hsum]
    _ = _ := by rw [Finset.sum_mul]



end D1Bound5
end
