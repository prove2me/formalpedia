-- Prove2me | solution 1 for FairSelling.vbarSum_insert_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:11:15.138826+00:00
-- url     : https://prove2.me/submissions/b921561c-f2f5-4f2d-9655-3e1353a981bb

import Mathlib
import Definitions.Def_RequestProject_Selling
open FairSelling
variable {G : Type*} [DecidableEq G]


theorem solution (w p : G → ℝ) (K : Finset G) (f : G) (hfK : f ∉ K) :
    vbarSum w p (K ∪ {f}) = vbarSum w p K + vbar w p f := by
  classical
  rw [show K ∪ {f} = insert f K by ext; simp [or_comm]]
  simp [vbarSum, hfK, add_comm]
