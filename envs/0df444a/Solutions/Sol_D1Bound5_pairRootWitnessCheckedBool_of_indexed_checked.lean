-- Prove2me | solution 1 for D1Bound5.pairRootWitnessCheckedBool_of_indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:13.27444+00:00
-- url     : https://prove2.me/submissions/fa55fed7-06d4-4099-8629-78f558459b20

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
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Theorems.Thm_D1Bound5_pairWitnessCandidateCoveredBool_of_indexed_checked

section
namespace D1Bound5
open QuadInt











/-- Indexed checking implies the previously accepted two-mutation witness
check, retaining exactly its root equations and sign coverage. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (w : PairRootWitness tau nu) (destinations : Option Nat × Option Nat)
    (hcheck : pairIndexedRootWitnessCheckedBool a b r0 bound vertices w destinations = true) :
    pairRootWitnessCheckedBool a b r0 bound vertices w = true := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  have hneighbors := Bool.and_eq_true_iff.mp hparts.2
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hparts.1, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact pairWitnessCandidateCoveredBool_of_indexed_checked bound vertices _
      destinations.1 hneighbors.1
  · exact pairWitnessCandidateCoveredBool_of_indexed_checked bound vertices _
      destinations.2 hneighbors.2







end D1Bound5
end
