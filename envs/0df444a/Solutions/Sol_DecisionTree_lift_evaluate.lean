-- Prove2me | solution 1 for DecisionTree.lift_evaluate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:43.93922+00:00
-- url     : https://prove2.me/submissions/855ef073-c2ec-4437-9db3-e4ab4b011319

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree

set_option autoImplicit true
open DecisionTree
namespace DecisionTree
theorem _root_.solution {h : n ≤ n'} {T : DecisionTree n} {I : Vector Bool n'} :
    (lift h T).evaluate I = T.evaluate (Vector.cast (show (min n n') = n by simpa) (I.take n)) := by
  cases T with
  | leaf => simp [lift, DecisionTree.evaluate]
  | branch _ _ _ =>
    simp only [lift, DecisionTree.evaluate]
    rw [solution]
    rw [solution]
    refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
    simp only [eq_iff_iff, Bool.coe_iff_coe, Fin.getElem_fin]
    rename_i a _ _
    have : (I.take n)[a.1] = I[a.1] := by
      apply Vector.getElem_take
    rw [← this]
    rfl
end DecisionTree
