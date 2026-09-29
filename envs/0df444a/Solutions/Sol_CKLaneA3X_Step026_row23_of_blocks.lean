-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:01:49.44991+00:00
-- url     : https://prove2.me/submissions/6077540c-f27e-4b4b-a205-d9fc50ae958b

import Mathlib.Data.List.GetD
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

set_option autoImplicit false

namespace A3XDecomposition
open CKLaneA3X

theorem list_eq_of_getD {α : Type} (d : α) {xs ys : List α}
    (hlen : xs.length = ys.length)
    (h : ∀ i, i < ys.length → xs.getD i d = ys.getD i d) : xs = ys := by
  apply List.ext_getElem hlen
  intro i hx hy
  simpa only [List.getD_eq_getElem xs d hx, List.getD_eq_getElem ys d hy] using h i hy

/-- Each structural and scalar premise is separately checkable. This theorem
does not assume that the numerical checks themselves have already passed. -/
theorem sparse_row_eq_of_entries (actual expected : SPoly)
    (hlen : actual.length = expected.length)
    (hindex : ∀ i, i < expected.length →
      (actual.getD i (0, [])).1 = (expected.getD i (0, [])).1)
    (hinner_length : ∀ i, i < expected.length →
      (actual.getD i (0, [])).2.length = (expected.getD i (0, [])).2.length)
    (hentry : ∀ i, i < expected.length → ∀ j,
      j < (expected.getD i (0, [])).2.length →
      (actual.getD i (0, [])).2.getD j (0, 0) =
        (expected.getD i (0, [])).2.getD j (0, 0)) : actual = expected := by
  apply list_eq_of_getD (0, []) hlen
  intro i hi
  apply Prod.ext
  · exact hindex i hi
  · exact list_eq_of_getD (0, 0) (hinner_length i hi) (hentry i hi)

theorem polynomial_eq_of_rows (actual expected : TPoly)
    (hlen : actual.length = expected.length)
    (hrow : ∀ i, i < expected.length → actual.getD i [] = expected.getD i []) :
    actual = expected := list_eq_of_getD [] hlen hrow

end A3XDecomposition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace A3XDecomposition
open CKLaneA3X

theorem sparse_row_eq_of_keys_and_blocks (actual expected : SPoly)
    (hkeys : actual.map Prod.fst = expected.map Prod.fst)
    (hblocks : ∀ i, i < expected.length →
      (actual.getD i (0, [])).2 = (expected.getD i (0, [])).2) :
    actual = expected := by
  have hlen : actual.length = expected.length := by
    simpa only [List.length_map] using congrArg List.length hkeys
  apply list_eq_of_getD (0, []) hlen
  intro i hi
  apply Prod.ext
  · have hi := congrArg (fun xs : List Nat => xs.getD i 0) hkeys
    simpa only [List.getD_map actual (0, []) Prod.fst,
      List.getD_map expected (0, []) Prod.fst] using hi
  · exact hblocks i hi

/-- Reconstruct the exact original degree-23 output row from 26 independently
checkable Laurent-polynomial blocks. The key/shape check is closed and proved
here; the numerical block equalities remain explicit premises. -/
theorem row23_of_blocks
    (hblocks : ∀ i : Fin 26,
      (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD i (0, [])).2 =
        ((D_mInner.P.getD 23 []).getD i (0, [])).2) :
    (TPoly.mulT D_m.P D_inner.P 24).getD 23 [] = D_mInner.P.getD 23 [] := by
  apply sparse_row_eq_of_keys_and_blocks
  · decide +kernel
  · intro i hi
    change i < 26 at hi
    exact hblocks ⟨i, hi⟩

end A3XDecomposition

theorem solution (hblocks : ∀ i : Fin 26,
      (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD i (0, [])).2 =
        ((D_mInner.P.getD 23 []).getD i (0, [])).2) : (TPoly.mulT D_m.P D_inner.P 24).getD 23 [] = D_mInner.P.getD 23 [] := A3XDecomposition.row23_of_blocks hblocks
