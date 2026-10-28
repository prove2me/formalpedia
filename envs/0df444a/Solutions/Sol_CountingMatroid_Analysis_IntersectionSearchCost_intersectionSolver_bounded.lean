-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearchCost.intersectionSolver_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:44:42.552317+00:00
-- url     : https://prove2.me/submissions/f5b3b978-117d-4012-8530-0aac0daaf771

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
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_augmentOnce_le

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

/-- INTERNAL: The explicit solver has fixed polynomial cost coefficients,
uniform even for oracle functions that are not matroid independence oracles.
TEXLINE: main.tex:283-289 -/
theorem solution :
    FeasibilityBounded intersectionSolver 100000 8 100000 8 := by
  intro n r o₁ o₂
  have hcoordinate (op : Op) :
      (intersectionSolver.run n r o₁ o₂).cost op ≤ 1000 * (n + r + 1) ^ 8 := by
    have hfold := cost_foldl_le
      (fun I (_ : ℕ) => augmentOnce o₁ o₂ I) (List.range r)
      (60 * (n + 1) ^ 5) (fun I _ op => cost_augmentOnce_le o₁ o₂ I op)
      (∅ : Finset (Fin n)) op
    simp only [List.length_range] at hfold
    have hsize : 1 ≤ n + r + 1 := by omega
    have hproduct : r * (n + 1) ^ 5 ≤ (n + r + 1) ^ 6 := by
      calc
        _ ≤ (n + r + 1) * (n + r + 1) ^ 5 := by gcongr <;> omega
        _ = (n + r + 1) ^ 6 := by ring
    have h68 : (n + r + 1) ^ 6 ≤ (n + r + 1) ^ 8 :=
      pow_le_pow_right₀ hsize (by omega)
    have hloopBound := Nat.mul_le_mul_left 60 (hproduct.trans h68)
    have hloadSize : n + 1 ≤ (n + r + 1) ^ 8 := by
      calc
        _ ≤ n + r + 1 := by omega
        _ ≤ (n + r + 1) ^ 8 := by
          simpa only [pow_one] using pow_le_pow_right₀ hsize (by omega : 1 ≤ 8)
    have hunit : 1 ≤ (n + r + 1) ^ 8 := one_le_pow₀ hsize
    have heq : Arlib.Computation.CostVec.one (Op.word .eq) op ≤ 1 := by
      simp only [Arlib.Computation.CostVec.one]
      split_ifs <;> omega
    unfold intersectionSolver
    simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply,
      Arlib.Computation.Charged.val_opMany, natEqual,
      Arlib.Computation.Charged.cost_op]
    calc
      _ ≤ r * (60 * (n + 1) ^ 5) + (n + 1 + 1) :=
        Nat.add_le_add hfold (Nat.add_le_add (cost_opMany_le _ _ _ _) heq)
      _ ≤ 1000 * (n + r + 1) ^ 8 := by nlinarith

  constructor
  · have hfirst := hcoordinate Op.oracleFirst
    have hsecond := hcoordinate Op.oracleSecond
    dsimp [oracleCalls]
    nlinarith
  · have hfold (l : List Arlib.Computation.Op) (acc : ℕ) :
        l.foldl (fun total instruction => total +
          (intersectionSolver.run n r o₁ o₂).cost (Op.word instruction)) acc ≤
          acc + l.length * (1000 * (n + r + 1) ^ 8) := by
      induction l generalizing acc with
      | nil => simp
      | cons instruction l ih =>
        simp only [List.foldl_cons, List.length_cons]
        have hhead := hcoordinate (Op.word instruction)
        have htail := ih (acc + (intersectionSolver.run n r o₁ o₂).cost
          (Op.word instruction))
        nlinarith
    have hwords := hfold Arlib.Computation.Op.all 0
    have hlength : Arlib.Computation.Op.all.length = 20 := rfl
    rw [hlength, Nat.zero_add] at hwords
    have hbit := hcoordinate Op.fairBit
    dsimp [otherSteps]
    nlinarith
