-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunOracleCalls.oracleCalls_repeatFor_indexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:06:59.908327+00:00
-- url     : https://prove2.me/submissions/3a119a92-cdaa-441c-a00a-9b91e68d7f20

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: Oracle charges add when charged computations are sequenced. -/
theorem oracleCalls_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    oracleCalls (p >>= f) = oracleCalls p + oracleCalls (f p.val) := by
  simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]



























end CountingMatroid.Analysis.ResourceBound

end

section


set_option autoImplicit false

/-!
# Oracle charges in one capped annealing run

The bounds below sum the two supplied independence-oracle charges through
the capped loops, including abort branches.
-/

namespace CountingMatroid.Analysis.BoundedRunOracleCalls

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines



open CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound







/-- INTERNAL: A state-independent continuation bound adds to the first charge. -/
theorem oracleCalls_bind_bound {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) (a b : ℕ)
    (hp : oracleCalls p ≤ a) (hf : ∀ x, oracleCalls (f x) ≤ b) :
    oracleCalls (p >>= f) ≤ a + b := by
  rw [oracleCalls_bind]
  exact Nat.add_le_add hp (hf p.val)

















end CountingMatroid.Analysis.BoundedRunOracleCalls

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · closed the oracle-call envelope by uniform chain, capped-return, restart, observation, and indexed phase-loop bounds; no new proof debt.
* recovery · blocked · verified the fourteen-declaration upstream extraction in Lean; completing the planned dependency move requires edits to ResourceBound, outside assigned ownership. No new proof debt introduced.
* r15 · open · separated oracle charges from rational-size invariants; direct boundedRun simplification leaves the nested phase charge, and the reusable primitive bounds are downstream in ResourceBound.
-/

end
set_option autoImplicit false

/-!
# Oracle charges in one capped annealing run

The bounds below sum the two supplied independence-oracle charges through
the capped loops, including abort branches.
-/

namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunOracleCalls

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines



open CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: A finite indexed loop only needs bounds at indices below its length. -/
theorem solution {β : Type}
    (f : ℕ → β → Arlib.Computation.Charged Op Cell β) (N k : ℕ)
    (h : ∀ j, j < N → ∀ b, oracleCalls (f j b) ≤ k) (b : β) :
    oracleCalls (Arlib.Computation.Charged.repeatFor f N b) ≤ N * k := by
  have hfold (l : List ℕ) (hl : ∀ j ∈ l, j < N) (b : β) :
      oracleCalls (Arlib.Computation.Charged.foldl (fun b j => f j b) l b) ≤
        l.length * k := by
    induction l generalizing b with
    | nil => simp [oracleCalls]
    | cons j js ih =>
        change oracleCalls (f j b >>= _) ≤ _
        calc
          _ ≤ k + js.length * k := by
            apply oracleCalls_bind_bound
            · exact h j (hl j (by simp)) b
            · intro next
              exact ih (fun i hi => hl i (by simp [hi])) next
          _ = (j :: js).length * k := by simp [Nat.add_mul]; omega
  exact (hfold (List.range N) (by simp) b).trans
    (by simp)
