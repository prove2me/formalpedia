-- Prove2me | solution 1 for FairSelling.trunc_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:58.0098+00:00
-- url     : https://prove2.me/submissions/9cfb7cd5-5a54-42ad-bc5c-2a86c02fceaf

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
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (g : G) : trunc w p t g ≤ max (p g) t :=
  max_le_max_left _ (min_le_right _ _)
end FairSelling
