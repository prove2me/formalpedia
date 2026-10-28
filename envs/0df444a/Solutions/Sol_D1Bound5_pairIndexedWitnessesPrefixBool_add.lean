-- Prove2me | solution 1 for D1Bound5.pairIndexedWitnessesPrefixBool_add
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:16.359975+00:00
-- url     : https://prove2.me/submissions/3e5b6e50-f6d6-421a-847c-4bd7e5160843

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







/-- Join two finite prefixes while preserving global destination indices. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (m n : ℕ) (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat)) :
    pairIndexedWitnessesPrefixBool a b r0 bound vertices (m + n) witnesses destinations =
      (pairIndexedWitnessesPrefixBool a b r0 bound vertices m witnesses destinations &&
        pairIndexedWitnessesPrefixBool a b r0 bound vertices n
          (witnesses.drop m) (destinations.drop m)) := by
  induction m generalizing witnesses destinations with
  | zero =>
      simp only [Nat.zero_add, pairIndexedWitnessesPrefixBool, List.drop_zero, Bool.true_and]
  | succ m ih =>
      cases witnesses with
      | nil =>
          cases destinations <;> cases n <;>
            simp [Nat.succ_add, pairIndexedWitnessesPrefixBool]
      | cons w ws =>
          cases destinations with
          | nil => simp [Nat.succ_add, pairIndexedWitnessesPrefixBool]
          | cons d ds =>
              rw [Nat.succ_add]
              change
                (pairIndexedRootWitnessCheckedBool a b r0 bound vertices w d &&
                  pairIndexedWitnessesPrefixBool a b r0 bound vertices (m+n) ws ds) =
                ((pairIndexedRootWitnessCheckedBool a b r0 bound vertices w d &&
                    pairIndexedWitnessesPrefixBool a b r0 bound vertices m ws ds) &&
                  pairIndexedWitnessesPrefixBool a b r0 bound vertices n
                    (ws.drop m) (ds.drop m))
              rw [ih ws ds, Bool.and_assoc]



end D1Bound5
end
