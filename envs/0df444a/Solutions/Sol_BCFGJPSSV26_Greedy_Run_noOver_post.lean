-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Run.noOver_post
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:55.668323+00:00
-- url     : https://prove2.me/submissions/38b54c75-5d6e-4ab3-938e-d03e769b1f11

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Structure
public import Mathlib.Data.Prod.Lex
public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
import all Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_noOver_pre
public import Theorems.Thm_BCFGJPSSV26_Greedy_noOver_partial

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

/-- No overbidding after every step. -/
theorem noOver_post {s : ℕ} (hs : s < R.len) :
    NoOver R.P R.X.d R.f (R.θpost s) (R.Dpre (s + 1)) := by
  rcases Nat.lt_or_ge (s + 1) R.len with h | h
  · rw [R.θpost_eq h]
    exact R.noOver_pre h
  · have hs' : s + 1 = R.len := by omega
    have hj : R.θpost s = R.P.θ R.P.R := by
      rw [R.θpost_eq_θ hs, hs', len, List.take_length, nRaise_steps]
    have h1 := noOver_partial R.good R.d1 R.f_nonneg R.sol.2.1 []
    rw [List.append_nil, R.sol.1, Par.θseq, Nat.mul_div_cancel_left _ two_pos] at h1
    rw [hj, hs', Dpre_len]
    exact h1

end Run

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Run.noOver_post := @BCFGJPSSV26.Greedy.Run.noOver_post
