-- Prove2me | solution 1 for CKLaneA3X.Step027.entryBounds_D_Us
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:00:15.527002+00:00
-- url     : https://prove2.me/submissions/ebd0eafc-b037-4914-846b-a87ae28408b8

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

private theorem a3x_bounds_list_eq (n : Nat) (xs ys : List ℚ)
    (hy : ys.length = n) (hx : xs.length = ys.length)
    (h : ∀ i : Fin n, xs.getD i 0 = ys.getD i 0) : xs = ys := by
  apply List.ext_getElem hx
  intro i hxi hyi
  have hi : i < n := by simpa only [hy] using hyi
  simpa only [List.getD_eq_getElem xs 0 hxi, List.getD_eq_getElem ys 0 hyi] using h ⟨i, hi⟩

theorem solution : entryBounds D_Us.P = [(0 : ℚ), (306381641655 : ℚ) / 549755813888, (0 : ℚ), (1499479667313 : ℚ) / 549755813888, (0 : ℚ), (2322557212633 : ℚ) / 1099511627776, (0 : ℚ), (3959951669649 : ℚ) / 549755813888, (0 : ℚ), (35073693232377 : ℚ) / 1099511627776, (0 : ℚ), (38934953257953 : ℚ) / 274877906944, (0 : ℚ), (586731665530877 : ℚ) / 1099511627776, (0 : ℚ), (8886011926605 : ℚ) / 4294967296, (0 : ℚ), (4149713315115945 : ℚ) / 549755813888, (0 : ℚ), (30998574873131219 : ℚ) / 1099511627776, (0 : ℚ), (14540618314931331 : ℚ) / 137438953472, (0 : ℚ), (338887962548126507 : ℚ) / 1099511627776] := by
  apply a3x_bounds_list_eq 24 _ _ (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel
