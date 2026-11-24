-- Prove2me | solution 1 for FairChores.cost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:14.549654+00:00
-- url     : https://prove2.me/submissions/7312c0a6-0c8b-448f-a7a9-8b510dcec6da

import Mathlib
import Definitions.Def_RequestProject_ChoresModel

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) {o : Outcome T n} (hvalid : o.Valid p) (j : Fin n) :
    0 ≤ cost c o j :=
  add_nonneg (Finset.sum_nonneg fun t _ => hc t) (hvalid.2.2.2.1 j)
end FairChores
