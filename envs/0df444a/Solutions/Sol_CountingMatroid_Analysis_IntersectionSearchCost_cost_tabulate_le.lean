-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearchCost.cost_tabulate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:52:07.59228+00:00
-- url     : https://prove2.me/submissions/352370e7-bae9-4c9f-955f-cac838c25c47

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

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Uniform resource obligation for the concrete capped exchange-graph solver.
The proved bound composes table and fold accounting through graph construction,
frozen breadth-first layers, sink selection, and at most `n` toggles, then
through the `r`-round solver.
It is independent of all matroid and exact-oracle promises.
-/

namespace CountingMatroid.Analysis.IntersectionSearchCost

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Every single-currency batch contributes at most its batch size
to any coordinate of the charged cost vector. -/
theorem cost_opMany_le {α : Type} (instruction : Op) (amount : ℕ) (value : α)
    (op : Op) :
    (Arlib.Computation.Charged.opMany instruction amount value :
      Arlib.Computation.Charged Op Cell α).cost op ≤ amount := by
  simp only [Arlib.Computation.Charged.cost_opMany, Arlib.Computation.CostVec.many]
  split_ifs <;> omega

/-- INTERNAL: A uniform coordinate bound on each body controls a charged fold. -/
theorem cost_foldl_le {α β : Type} (f : β → α → Arlib.Computation.Charged Op Cell β)
    (l : List α) (k : ℕ) (hf : ∀ b a op, (f b a).cost op ≤ k)
    (b : β) (op : Op) :
    (Arlib.Computation.Charged.foldl f l b).cost op ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [Arlib.Computation.Charged.cost_foldl_cons]
    simp only [Pi.add_apply, List.length_cons]
    have hhead := hf b a op
    have htail := ih (f b a).val
    nlinarith



























end CountingMatroid.Analysis.IntersectionSearchCost

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · proved · closed the unconditional cost certificate by coordinate bounds through table construction, capped search, toggles, and the rank-many loop; no oracle promise is used.
-/

end
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

/-- INTERNAL: Materializing a table pays allocation, all entry evaluations,
and all charged overwrites; the bound holds for every starting oracle. -/
theorem solution {n : ℕ} {α : Type} [Inhabited α]
    (width k : ℕ) (f : Fin n → Arlib.Computation.Charged Op Cell α)
    (hf : ∀ i op, (f i).cost op ≤ k) (op : Op) :
    (tabulate width f).cost op ≤
      (n * width + 1) + n * (k + (n * width + 1)) := by
  let step := fun (table : Fin n → α) (i : Fin n) => do
    let value ← f i
    Arlib.Computation.Charged.opMany (Op.word .store) (n * width + 1)
      (Function.update table i value)
  have hstep (table : Fin n → α) (i : Fin n) (op : Op) :
      (step table i).cost op ≤ k + (n * width + 1) := by
    simp only [step, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
    exact Nat.add_le_add (hf i op) (cost_opMany_le _ _ _ _)
  have hfold := cost_foldl_le step (List.finRange n)
    (k + (n * width + 1)) hstep
    (fun _ => (default : α)) op
  simp only [List.length_finRange] at hfold
  unfold tabulate
  simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply,
    Arlib.Computation.Charged.val_opMany]
  exact Nat.add_le_add (cost_opMany_le _ _ _ _) hfold
