-- Prove2me | solution 1 for D1Bound5.pairIndexedWitnessesCheckedBool_eq_prefix_drop
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:19.02644+00:00
-- url     : https://prove2.me/submissions/34a4a532-c85b-430b-895c-3690c46202bd

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
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt



/-- Exact factorization, including mismatched lists. Both mutation signs
and their lookups in the original vertex list are unchanged. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (n : ℕ) (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat)) :
    pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations =
      (pairIndexedWitnessesPrefixBool a b r0 bound vertices n witnesses destinations &&
        pairIndexedWitnessesCheckedBool a b r0 bound vertices
          (witnesses.drop n) (destinations.drop n)) := by
  induction n generalizing witnesses destinations with
  | zero =>
      simp only [pairIndexedWitnessesPrefixBool, List.drop_zero, Bool.true_and]
  | succ n ih =>
      cases witnesses with
      | nil => cases destinations <;> rfl
      | cons w ws =>
          cases destinations with
          | nil => rfl
          | cons d ds =>
              change
                (pairIndexedRootWitnessCheckedBool a b r0 bound vertices w d &&
                  pairIndexedWitnessesCheckedBool a b r0 bound vertices ws ds) =
                ((pairIndexedRootWitnessCheckedBool a b r0 bound vertices w d &&
                    pairIndexedWitnessesPrefixBool a b r0 bound vertices n ws ds) &&
                  pairIndexedWitnessesCheckedBool a b r0 bound vertices
                    (ws.drop n) (ds.drop n))
              rw [ih ws ds, Bool.and_assoc]







end D1Bound5
end
