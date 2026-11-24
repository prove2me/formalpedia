-- Prove2me | solution 1 for FairSelling.le_minUtil_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:54.363554+00:00
-- url     : https://prove2.me/submissions/50361f27-1d81-4e19-b547-d5321a858962

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v : G → ℝ) (o : Outcome G n) (r : ℝ) :
    r ≤ minUtil v o ↔ ∀ j, r ≤ util v o j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [minUtil, le_ciInf_iff (Finite.bddBelow_range _)]
end FairSelling
