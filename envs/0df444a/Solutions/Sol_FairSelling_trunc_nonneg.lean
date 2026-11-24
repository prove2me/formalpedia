-- Prove2me | solution 1 for FairSelling.trunc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:41.024911+00:00
-- url     : https://prove2.me/submissions/c1b923d5-6a92-47f0-93b5-d68fd2927044

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
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ trunc w p t g :=
  le_trans (hp g) (le_max_left _ _)
end FairSelling
