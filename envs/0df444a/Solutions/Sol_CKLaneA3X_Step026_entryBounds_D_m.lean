-- Prove2me | solution 1 for CKLaneA3X.Step026.entryBounds_D_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:38:49.733514+00:00
-- url     : https://prove2.me/submissions/8ec39c00-1160-445c-abd6-b455a67c6b35

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

private theorem a3x_bounds_list_eq (n : Nat) (xs ys : List ℚ)
    (hy : ys.length = n) (hx : xs.length = ys.length)
    (h : ∀ i : Fin n, xs.getD i 0 = ys.getD i 0) : xs = ys := by
  apply List.ext_getElem hx
  intro i hxi hyi
  have hi : i < n := by simpa only [hy] using hyi
  simpa only [List.getD_eq_getElem xs 0 hxi, List.getD_eq_getElem ys 0 hyi] using h ⟨i, hi⟩

theorem solution : entryBounds D_m.P = [(0 : ℚ), (0 : ℚ), (306381641655 : ℚ) / 549755813888, (0 : ℚ), (4625113140225 : ℚ) / 1099511627776, (0 : ℚ), (2051115671423 : ℚ) / 274877906944, (0 : ℚ), (19033699474239 : ℚ) / 1099511627776, (0 : ℚ), (62507000350669 : ℚ) / 1099511627776, (0 : ℚ), (234993017543595 : ℚ) / 1099511627776, (0 : ℚ), (237413709769809 : ℚ) / 274877906944, (0 : ℚ), (3424265701537063 : ℚ) / 1099511627776, (0 : ℚ), (3674766318159601 : ℚ) / 274877906944, (0 : ℚ), (26362714378386645 : ℚ) / 549755813888, (0 : ℚ), (226933924535320069 : ℚ) / 1099511627776, (0 : ℚ)] := by
  apply a3x_bounds_list_eq 24 _ _ (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel
