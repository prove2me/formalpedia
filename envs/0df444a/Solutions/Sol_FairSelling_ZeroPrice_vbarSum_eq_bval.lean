-- Prove2me | solution 1 for FairSelling.ZeroPrice.vbarSum_eq_bval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:45.506845+00:00
-- url     : https://prove2.me/submissions/8a2a9c0b-3a28-4195-a5f2-55a31d6bbe3a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling.ZeroPrice
theorem _root_.solution (w p : G → ℝ) (hp0 : ∀ g, p g = 0) (hw : ∀ g, 0 ≤ w g) (S : Finset G) :
    vbarSum w p S = bval w S := by
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp [vbar, hp0 g, max_eq_right (hw g)]
end FairSelling.ZeroPrice
