-- Prove2me | solution 1 for FairSelling.truncBundle_le_vbarSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:34.887621+00:00
-- url     : https://prove2.me/submissions/d9fb2d4e-2d2b-47cd-9d93-cfc6887e5207

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Theorems.Thm_FairSelling_trunc_le_vbar

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (R : Finset G) :
    truncBundle w p t R ≤ vbarSum w p R :=
  Finset.sum_le_sum (fun g _ => trunc_le_vbar w p t g)
end FairSelling
