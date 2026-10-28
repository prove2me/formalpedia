-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearchCost.cost_initialPaths_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:08:29.717708+00:00
-- url     : https://prove2.me/submissions/9eeeaa3a-d1c6-4900-a1c4-359692583cc2

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_tabulate_le

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Uniform resource obligation for the concrete capped exchange-graph solver.
The proved bound composes table and fold accounting through graph construction,
frozen breadth-first layers, sink selection, and at most `n` toggles, then
through the `r`-round solver.
It is independent of all matroid and exact-oracle promises.
-/

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionSearchCost

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Allocating and initializing source paths costs cubically. -/
theorem solution {n : ℕ} (g : ExchangeGraph n) (op : Op) :
    (initialPaths g).cost op ≤ 10 * (n + 1) ^ 3 := by
  have hbody (i : Fin n) (op : Op) :
      (do
        let terminal ← Arlib.Computation.Charged.opMany (Op.word .load) (2 * n + 1)
          (g.terminals i)
        if terminal.1 then
          Arlib.Computation.Charged.op (Op.word .store) (some [i])
        else pure none : Arlib.Computation.Charged Op Cell (Option (List (Fin n)))).cost op ≤
          2 * n + 2 := by
    cases ht : (g.terminals i).1 <;>
      simp [ht, Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
      split_ifs <;> omega
  have h := cost_tabulate_le (n + 1) (2 * n + 2) _ hbody op
  exact h.trans (by nlinarith)
