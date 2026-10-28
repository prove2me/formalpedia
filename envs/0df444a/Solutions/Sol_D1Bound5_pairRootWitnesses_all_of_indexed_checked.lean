-- Prove2me | solution 1 for D1Bound5.pairRootWitnesses_all_of_indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:59.386986+00:00
-- url     : https://prove2.me/submissions/6968d10b-1495-4195-a5ff-db05044109e0

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
import Theorems.Thm_D1Bound5_pairRootWitnessCheckedBool_of_indexed_checked

section
namespace D1Bound5
open QuadInt













/-- The lockstep checker validates every witness in the original list. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hcheck : pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations = true) :
    witnesses.all (pairRootWitnessCheckedBool a b r0 bound vertices) = true := by
  induction witnesses generalizing destinations with
  | nil => rfl
  | cons w ws ih =>
      cases destinations with
      | nil => simp only [pairIndexedWitnessesCheckedBool, Bool.false_eq_true] at hcheck
      | cons d ds =>
          have hparts := Bool.and_eq_true_iff.mp hcheck
          change (pairRootWitnessCheckedBool a b r0 bound vertices w &&
            ws.all (pairRootWitnessCheckedBool a b r0 bound vertices)) = true
          exact Bool.and_eq_true_iff.mpr
            ⟨pairRootWitnessCheckedBool_of_indexed_checked a b r0 bound vertices w d hparts.1,
              ih ds hparts.2⟩





end D1Bound5
end
