-- Prove2me | solution 1 for CKLaneA3X.Step026.entryBounds_D_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:38:50.384629+00:00
-- url     : https://prove2.me/submissions/d726e139-58d5-4cfa-8dc8-966d9d04ce8e

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

theorem solution : entryBounds D_inner.P = [(0 : ℚ), (2451053133237 : ℚ) / 1099511627776, (0 : ℚ), (7804116504201 : ℚ) / 1099511627776, (0 : ℚ), (13522484094635 : ℚ) / 549755813888, (0 : ℚ), (119550119947271 : ℚ) / 1099511627776, (0 : ℚ), (312317938243881 : ℚ) / 549755813888, (0 : ℚ), (2830579640422985 : ℚ) / 1099511627776, (0 : ℚ), (13458671255452477 : ℚ) / 1099511627776, (0 : ℚ), (30066067898006947 : ℚ) / 549755813888, (0 : ℚ), (254015746060502207 : ℚ) / 1099511627776, (0 : ℚ), (1121945005055783035 : ℚ) / 1099511627776, (0 : ℚ), (1183201062237625867 : ℚ) / 274877906944, (0 : ℚ), (3441045752199252747 : ℚ) / 1099511627776] := by
  apply a3x_bounds_list_eq 24 _ _ (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel
