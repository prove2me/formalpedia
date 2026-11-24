-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.piPowDivFactorialLt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:14.214402+00:00
-- url     : https://prove2.me/submissions/4d7fa443-ccfe-4521-84b4-92edfb48588e

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
theorem _root_.solution : PiPowFactorial := by
  intro k hk
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  have key : ∀ m : ℕ, (3.15:ℝ) ^ (m + 3 + 1) ≤ 17 * ((m + 3).factorial : ℝ) := by
    intro m
    induction m with
    | zero => norm_num [Nat.factorial]
    | succ m ih =>
      rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast at ih ⊢
      have hf : (0:ℝ) ≤ ((m + 3).factorial : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) hf]
  have bound : (3.15:ℝ) ^ (n + 1) ≤ 17 * (n.factorial : ℝ) := by
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
    · subst h; norm_num [Nat.factorial]
    · subst h; norm_num [Nat.factorial]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact key m
  have hlt : Real.pi ^ (n + 1) < (3.15:ℝ) ^ (n + 1) :=
    pow_lt_pow_left₀ hπ hπ0.le (Nat.succ_ne_zero n)
  rw [div_lt_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  linarith
end Formalism.HermitianLatticeCounting.P
