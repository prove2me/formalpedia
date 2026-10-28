-- Prove2me | solution 1 for D1Bound5.pairClosureIndexedWitnessBool_of_checked_parts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:16.799427+00:00
-- url     : https://prove2.me/submissions/5327cd15-618b-45f7-a2f5-7a16a8567581

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









/-- Ordered coverage and the anchor-root equation remain separate mandatory
checks when the mutation-witness computation is partitioned. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hcoverage : decide (r0 * r0 = a * b + 1 ∧
      witnesses.map PairRootWitness.vertex = vertices) = true)
    (hwitnesses : pairIndexedWitnessesCheckedBool a b r0 bound vertices
      witnesses destinations = true) :
    pairClosureIndexedWitnessBool a b r0 bound vertices witnesses destinations = true :=
  Bool.and_eq_true_iff.mpr ⟨hcoverage, hwitnesses⟩

end D1Bound5
end
