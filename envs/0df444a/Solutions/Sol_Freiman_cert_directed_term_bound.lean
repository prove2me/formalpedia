-- Prove2me | solution 1 for Freiman.cert_directed_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:33:48.465032+00:00
-- url     : https://prove2.me/submissions/2f274531-8526-4dd1-a68a-41c91de7fc61

import Definitions.Def_Freiman_certificates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators


theorem solution :
    ∀ (q lo hi : ℚ) (x : ℝ), (lo:ℝ) ≤ x → x ≤ hi → (certDirectedTerm q lo hi:ℝ) ≤ (q:ℝ)*x := by
  intro q lo hi x hlo hhi
  unfold certDirectedTerm
  split_ifs with h
  · push_cast
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast h)
  · push_cast
    exact mul_le_mul_of_nonpos_left hhi (by exact_mod_cast (le_of_lt (lt_of_not_ge h)))


#print axioms solution
