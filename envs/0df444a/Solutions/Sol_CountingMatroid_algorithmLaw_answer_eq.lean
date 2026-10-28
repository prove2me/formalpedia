-- Prove2me | solution 1 for CountingMatroid.algorithmLaw_answer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:09:45.093341+00:00
-- url     : https://prove2.me/submissions/cf9f830e-9f37-45a5-948c-481c711a48c4

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
import Theorems.Thm_CountingMatroid_estimate_answer_eq

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

/-- Both laws draw the same finite fair-bit blocks and use the same exhausted-block convention. Apply pointwise answer equality under that common PMF; no lazy-versus-up-front sampling lemma is needed here. -/
theorem solution (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Model.Run.algorithmLaw solver n r o₁ o₂ p).map Arlib.Computation.Charged.val = CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p := by
  unfold CountingMatroid.Model.Run.algorithmLaw CountingMatroid.Interface.Pseudocode.estimateLaw
  simp only [schedule_value_eq]
  change PMF.map Arlib.Computation.Charged.val
      (PMF.map (fun blocks => CountingMatroid.Program.estimate solver n r o₁ o₂ p
        (CountingMatroid.Model.Run.blockTape blocks))
        (CountingMatroid.Model.Run.fairBlocks
          (CountingMatroid.Interface.Pseudocode.setup n p).repetitions
          (CountingMatroid.Model.Run.blockLength n r p))) =
      PMF.map (fun blocks => CountingMatroid.Interface.Pseudocode.estimate solver n r o₁ o₂ p
        (CountingMatroid.Model.Run.blockTape blocks))
        (CountingMatroid.Model.Run.fairBlocks
          (CountingMatroid.Interface.Pseudocode.setup n p).repetitions
          (CountingMatroid.Model.Run.blockLength n r p))
  rw [PMF.map_comp]
  congr 1
  funext blocks
  exact estimate_answer_eq solver n r o₁ o₂ p (CountingMatroid.Model.Run.blockTape blocks)
