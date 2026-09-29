-- Prove2me | solution 1 for CKLaneA3X.Step026.row21_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:15:10.456637+00:00
-- url     : https://prove2.me/submissions/32eabdcd-a40e-4aa5-8c6b-2e79ec699fd3

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

private theorem a3x_list_eq_of_getD {α : Type} (d : α) {xs ys : List α}
    (hlen : xs.length = ys.length)
    (h : ∀ i, i < ys.length → xs.getD i d = ys.getD i d) : xs = ys := by
  apply List.ext_getElem hlen
  intro i hx hy
  simpa only [List.getD_eq_getElem xs d hx, List.getD_eq_getElem ys d hy] using h i hy

private theorem a3x_sparse_row_eq_of_keys_and_blocks (actual expected : SPoly)
    (hkeys : actual.map Prod.fst = expected.map Prod.fst)
    (hblocks : ∀ i, i < expected.length →
      (actual.getD i (0, [])).2 = (expected.getD i (0, [])).2) :
    actual = expected := by
  have hlen : actual.length = expected.length := by
    simpa only [List.length_map] using congrArg List.length hkeys
  apply a3x_list_eq_of_getD (0, []) hlen
  intro i hi
  apply Prod.ext
  · have hi := congrArg (fun xs : List Nat => xs.getD i 0) hkeys
    simpa only [List.getD_map actual (0, []) Prod.fst,
      List.getD_map expected (0, []) Prod.fst] using hi
  · exact hblocks i hi

theorem solution (hblocks : ∀ i : Fin 24, (((TPoly.mulT D_m.P D_inner.P 24).getD 21 []).getD i (0, [])).2 = ((D_mInner.P.getD 21 []).getD i (0, [])).2) : (TPoly.mulT D_m.P D_inner.P 24).getD 21 [] = D_mInner.P.getD 21 [] := by
  apply a3x_sparse_row_eq_of_keys_and_blocks
  · decide +kernel
  · intro i hi
    change i < 24 at hi
    exact hblocks ⟨i, hi⟩
