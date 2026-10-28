-- Prove2me | solution 1 for CountingMatroid.Analysis.RankOneFeasibility.singletonScan_costs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:52:23.381786+00:00
-- url     : https://prove2.me/submissions/1a385b86-446c-4603-901b-2fcb0ce6df1d

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
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
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility
end CountingMatroid.Analysis.RankOneFeasibility
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

/-- INTERNAL: Exact resource counts for the singleton scan, uniform even for
oracles that do not represent matroids. Each singleton uses two oracle calls,
one insertion, quadratic query encoding, and two Boolean operations.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (o₁ o₂ : IndependenceOracle n) :
    oracleCalls (singletonScan o₁ o₂) = 2 * n ∧
      otherSteps (singletonScan o₁ o₂) = n * (n * (n + 1) + 3) := by
  let price (op : Op) :=
    (if op = Op.word .store then 1 else 0) +
    (if op = Op.word .load then n * (n + 1) else 0) +
    (if op = Op.oracleFirst then 1 else 0) +
    (if op = Op.oracleSecond then 1 else 0) +
    (if op = Op.word .band then 1 else 0) +
    (if op = Op.word .bor then 1 else 0)
  have hstep (found : Bool) (i : Fin n) (op : Op) :
      (singletonStep o₁ o₂ found i).cost op = price op := by
    simp [singletonStep, insertElement, encodeQuery, oracleQuery, price,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many, Nat.add_assoc]
  have hfold (l : List (Fin n)) (found : Bool) (op : Op) :
      (Arlib.Computation.Charged.foldl (singletonStep o₁ o₂) l found).cost op =
        l.length * price op := by
    induction l generalizing found with
    | nil => simp
    | cons i l ih =>
        rw [Arlib.Computation.Charged.cost_foldl_cons]
        simp only [Pi.add_apply, hstep, ih, List.length_cons]
        ring
  have hcost (op : Op) : (singletonScan o₁ o₂).cost op = n * price op := by
    simpa only [singletonScan, List.length_finRange] using
      hfold (List.finRange n) false op
  constructor
  · simp [oracleCalls, hcost, price]
    omega
  · simp [otherSteps, hcost, price, Arlib.Computation.Op.all]
    ring
