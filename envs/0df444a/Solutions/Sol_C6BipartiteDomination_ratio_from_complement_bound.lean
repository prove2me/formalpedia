-- Prove2me | solution 1 for C6BipartiteDomination.ratio_from_complement_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:40:30.375824+00:00
-- url     : https://prove2.me/submissions/cf65c135-987b-46d1-b6c3-526833567494

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic
import Definitions.Def_C6BipartiteDomination_Basic

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {d w : ℕ}
    (h : 8 * w ≥ 7 * d) : 15 * d ≤ 8 * (d + w) := by
  omega
end C6BipartiteDomination
