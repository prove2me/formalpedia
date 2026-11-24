-- Prove2me | solution 1 for FairSelling.trunc_le_vbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:53.804515+00:00
-- url     : https://prove2.me/submissions/97f67ab6-de47-4634-93d3-ee3d131dd07f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (g : G) : trunc w p t g ≤ vbar w p g :=
  max_le_max_left _ (min_le_left _ _)
end FairSelling
