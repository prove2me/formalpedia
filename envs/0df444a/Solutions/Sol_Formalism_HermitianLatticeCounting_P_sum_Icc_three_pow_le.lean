-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sum_Icc_three_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:31.531074+00:00
-- url     : https://prove2.me/submissions/7ddff3f8-f861-47fc-96b9-0c6e83dbaf1d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ j ∈ Finset.Icc 3 N, x ^ j ≤ x ^ 3 / (1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  have key : ∀ n, (1 - x) * ∑ j ∈ Finset.Icc 3 (n + 2), x ^ j = x ^ 3 - x ^ (n + 3) := by
    intro n
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (show ¬ 3 ≤ 0 + 2 by norm_num)]
      simp
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by ring,
        Finset.sum_Icc_succ_top (show 3 ≤ n + 2 + 1 by omega), mul_add, ih]
      ring
  rw [le_div_iff₀ h1x]
  rcases (show N ≤ 1 ∨ 2 ≤ N by omega) with h | h
  · rw [Finset.Icc_eq_empty (show ¬ 3 ≤ N by omega), Finset.sum_empty, zero_mul]; positivity
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [mul_comm, key n]
    have : 0 ≤ x ^ (n + 3) := by positivity
    linarith
end Formalism.HermitianLatticeCounting.P
