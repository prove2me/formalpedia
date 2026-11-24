-- Prove2me | solution 1 for FairSelling.truncBundle_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:48.60018+00:00
-- url     : https://prove2.me/submissions/1257e099-a861-46d6-ace1-66dabfec47f6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Theorems.Thm_FairSelling_trunc_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (hp : ∀ g, 0 ≤ p g) (R : Finset G) :
    0 ≤ truncBundle w p t R :=
  Finset.sum_nonneg (fun g _ => trunc_nonneg w p t hp g)
end FairSelling
