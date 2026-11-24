-- Prove2me | solution 1 for FairSelling.truncBundle_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:54.439061+00:00
-- url     : https://prove2.me/submissions/c87f1fed-3e3b-4f6a-8c9e-e9d18d612b0e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (t : ℝ) {R X : Finset G} (h : X ⊆ R) :
    truncBundle w p t R = truncBundle w p t (R \ X) + truncBundle w p t X :=
  (Finset.sum_sdiff h).symm
end FairSelling
