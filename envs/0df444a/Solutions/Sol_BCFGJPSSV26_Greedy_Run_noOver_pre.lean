-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Run.noOver_pre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:17.177159+00:00
-- url     : https://prove2.me/submissions/83727f5f-73dd-4a51-a363-440fbd10a948

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Structure
public import Mathlib.Data.Prod.Lex
public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
import all Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Theorems.Thm_BCFGJPSSV26_Greedy_noOver_partial

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

/-- No overbidding before every step, for the profile of the prefix. -/
theorem noOver_pre {s : ℕ} (hs : s < R.len) : NoOver R.P R.X.d R.f (R.θs s) (R.Dpre s) := by
  obtain ⟨hp, t, -, hpre, -, -⟩ := R.step_spec hs
  have hv := etaValid_take R.sol.2.1 (R.step s).seq
  have h := noOver_partial R.good R.d1 R.f_nonneg hv ((R.H.getD (R.step s).seq []).take t)
  rw [List.length_take, min_eq_left (by rw [R.sol.1]; omega)] at h
  rw [Dpre, hpre]
  exact h

end Run

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Run.noOver_pre := @BCFGJPSSV26.Greedy.Run.noOver_pre
