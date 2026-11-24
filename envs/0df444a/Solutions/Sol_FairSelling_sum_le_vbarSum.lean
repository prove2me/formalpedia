-- Prove2me | solution 1 for FairSelling.sum_le_vbarSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:33.581416+00:00
-- url     : https://prove2.me/submissions/bc103451-166e-4b15-bcee-24f6a1bd757f

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (A : Finset G) : ∑ g ∈ A, w g ≤ vbarSum w p A :=
  Finset.sum_le_sum (fun _ _ => le_max_right _ _)
end FairSelling
