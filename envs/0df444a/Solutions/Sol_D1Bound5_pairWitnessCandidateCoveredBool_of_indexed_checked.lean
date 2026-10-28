-- Prove2me | solution 1 for D1Bound5.pairWitnessCandidateCoveredBool_of_indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:17.907278+00:00
-- url     : https://prove2.me/submissions/48094211-7256-423c-a97c-9cb4cf935cc6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt









/-- Every accepted indexed candidate satisfies the original membership
checker. In-range lookup is required by `getElem? = some w` itself. -/
theorem _root_.solution {tau nu : ℤ}
    (bound : ℤ) (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu)
    (destination : Option Nat)
    (hcheck : pairIndexedCandidateCoveredBool bound vertices w destination = true) :
    pairWitnessCandidateCoveredBool bound vertices w = true := by
  cases destination with
  | none =>
      change decide (bound < w.norm) = true at hcheck
      have hout : bound < w.norm := of_decide_eq_true hcheck
      simp [pairWitnessCandidateCoveredBool, not_le.mpr hout]
  | some i =>
      change decide (vertices[i]? = some w) = true at hcheck
      have hlookup : vertices[i]? = some w := of_decide_eq_true hcheck
      have hmem : w ∈ vertices := List.mem_of_getElem? hlookup
      simp [pairWitnessCandidateCoveredBool, hmem]









end D1Bound5
end
