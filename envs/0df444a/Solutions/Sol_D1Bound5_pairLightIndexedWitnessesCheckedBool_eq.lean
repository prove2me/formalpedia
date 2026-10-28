-- Prove2me | solution 1 for D1Bound5.pairLightIndexedWitnessesCheckedBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:01.213649+00:00
-- url     : https://prove2.me/submissions/ab123bbc-0150-4621-8041-083aa53c45f8

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosureBridge_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Theorems.Thm_D1Bound5_pairLightIndexedRootWitnessCheckedBool_eq

section
namespace D1Bound5













/-- Exact identity of the complete lockstep check, retaining rejection of any
unmatched tail and all globally indexed mutations of both signs. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat)) :
    pairLightIndexedWitnessesCheckedBool tau nu
      (pairLightCoordinates a) (pairLightCoordinates b) (pairLightCoordinates r0) bound
      (vertices.map pairLightCoordinates) (witnesses.map pairLightRootWitnessCoordinates)
      destinations =
      pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations := by
  induction witnesses generalizing destinations with
  | nil => cases destinations <;> rfl
  | cons w ws ih =>
      cases destinations with
      | nil => rfl
      | cons d ds =>
          simp only [List.map_cons, pairLightIndexedWitnessesCheckedBool,
            pairIndexedWitnessesCheckedBool, pairLightIndexedRootWitnessCheckedBool_eq, ih]

end D1Bound5
end
