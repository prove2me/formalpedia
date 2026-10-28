-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearch.tabulate_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:50:49.960144+00:00
-- url     : https://prove2.me/submissions/117515a3-6219-4811-b680-c823c73dfc2f

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

namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Concrete bounded exchange-graph search for the feasibility pretest. Oracle
answers are obtained only through `oracleQuery`; the graph, path tables, and
set updates are charged. Breadth-first layers use a frozen previous table,
so the first path recorded at a vertex has minimum length. Path lists are
capped at `n` entries, and the outer solver performs exactly `r` augmentations.
The elementary query specifications are proved here. The common-independence
and maximum-cardinality theorem and the uniform cost certificate belong to
separate proof files.
-/

namespace CountingMatroid.Analysis.IntersectionSearch
end CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionSearch

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

/-- INTERNAL: Filling every ground index writes exactly the tested entry. -/
theorem solution {n : ℕ} {α : Type} [Inhabited α] (width : ℕ)
    (f : Fin n → Arlib.Computation.Charged Op Cell α) :
    (tabulate width f).val = fun i => (f i).val := by
  have hfold (l : List (Fin n)) (table : Fin n → α) (i : Fin n) :
      (Arlib.Computation.Charged.foldl (fun table j => do
        let value ← f j
        Arlib.Computation.Charged.opMany (Op.word .store) (n * width + 1)
          (Function.update table j value)) l table).val i =
        if i ∈ l then (f i).val else table i := by
    induction l generalizing table with
    | nil => simp
    | cons j l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      simp only [Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_opMany, ih]
      by_cases hij : i = j
      · subst i
        simp
      · simp [List.mem_cons, hij, Function.update_of_ne hij]
  funext i
  simpa only [tabulate, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_opMany, List.mem_finRange, if_true] using
    hfold (List.finRange n) (fun _ => default) i
