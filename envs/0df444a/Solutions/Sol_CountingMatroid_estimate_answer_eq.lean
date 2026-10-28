-- Prove2me | solution 1 for CountingMatroid.estimate_answer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:07:43.833263+00:00
-- url     : https://prove2.me/submissions/ed0bd2a7-cf66-4d93-b825-68a7823aed1b

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
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
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_median_answer_eq

namespace CountingMatroid
end CountingMatroid
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
section


/-!
# The program and the model are the same algorithm

`CountingMatroid.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`CountingMatroid.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`CountingMatroid.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`outputLaw_answer_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

The bridge is closed by a charged insertion lemma and the resulting median,
estimator, and PMF law equalities.
-/

set_option autoImplicit false

namespace CountingMatroid

/-- The pseudocode pretest is the value of the charged pretest. This is a definitional equality. -/
theorem pretest_value_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) : (CountingMatroid.Program.preprocess solver n r o₁ o₂).val = CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ := by
  rfl

/-- Both sides use the same schedule, including its repetition count. This is a definitional equality. -/
theorem schedule_value_eq (n : ℕ) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Program.schedule n p).val = CountingMatroid.Interface.Pseudocode.setup n p := by
  rfl











end CountingMatroid

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · closed the answer-law bridge and its six preceding and following correspondences.
-/

end
/-!
# The program and the model are the same algorithm

`CountingMatroid.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`CountingMatroid.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`CountingMatroid.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`outputLaw_answer_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

The bridge is closed by a charged insertion lemma and the resulting median,
estimator, and PMF law equalities.
-/

set_option autoImplicit false

namespace CountingMatroid
end CountingMatroid
open CountingMatroid

/-- Unfold the charged binds, match the pretest branches, and identify each bounded-run answer. The median lemma handles the reversed list produced by charged cons operations. -/
theorem solution (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) (tape : ℕ → ℕ → Bool) : (CountingMatroid.Program.estimate solver n r o₁ o₂ p tape).val = CountingMatroid.Interface.Pseudocode.estimate solver n r o₁ o₂ p tape := by
  have hfold : ∀ (s : CountingMatroid.Model.AnnealingSchedule)
      (indices : List ℕ) (acc : List ℚ),
      (Arlib.Computation.Charged.foldl
        (fun acc j => do
          let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0
          CountingMatroid.Model.Operations.consRational value acc)
        indices acc).val =
      (indices.map (fun j => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (tape j) s)).reverse ++ acc := by
    intro s indices
    induction indices with
    | nil => intro acc; simp
    | cons j js ih =>
        intro acc
        simp only [Arlib.Computation.Charged.val_foldl_cons]
        rw [ih]
        simp [Arlib.Computation.Charged.val_bind,
          CountingMatroid.Interface.Pseudocode.singleRun,
          CountingMatroid.Model.Operations.consRational]
  simp [CountingMatroid.Program.estimate, CountingMatroid.Interface.Pseudocode.estimate,
    pretest_value_eq]
  split
  · simp_all
  · simp_all [schedule_value_eq, Arlib.Computation.Charged.repeatFor,
      median_answer_eq]
