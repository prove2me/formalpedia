-- Prove2me | solution 1 for D1Bound5.pairClosureBool_of_witness_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:23:17.211615+00:00
-- url     : https://prove2.me/submissions/3d3ab8e3-6097-4077-a987-f6286231fe9f

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
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_pairClosure_of_witness_checked

section
namespace D1Bound5
open QuadInt



















/-- A witness certificate proves the original Boolean closure certificate.
Consumers such as `small_pair_graph_excludes_three_full_ring` need no change. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (hcheck : pairClosureWitnessBool a b r0 bound vertices witnesses = true) :
    pairClosureBool a b bound vertices = true := by
  apply List.all_eq_true.mpr
  intro z hz
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases hbound : (pairMutationPlus a b z).norm ≤ bound
    · have hmem := pairClosure_of_witness_checked hd a b r0 bound vertices witnesses
        hcheck hz (Or.inl rfl) hbound
      simp [hbound, hmem]
    · simp [hbound]
  · by_cases hbound : (pairMutationMinus a b z).norm ≤ bound
    · have hmem := pairClosure_of_witness_checked hd a b r0 bound vertices witnesses
        hcheck hz (Or.inr rfl) hbound
      simp [hbound, hmem]
    · simp [hbound]

end D1Bound5
end
