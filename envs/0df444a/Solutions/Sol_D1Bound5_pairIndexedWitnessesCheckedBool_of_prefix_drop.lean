-- Prove2me | solution 1 for D1Bound5.pairIndexedWitnessesCheckedBool_of_prefix_drop
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:01:49.470019+00:00
-- url     : https://prove2.me/submissions/618f3bde-8119-447b-b623-1871be6eaae4

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
import Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_eq_prefix_drop

section
namespace D1Bound5
open QuadInt





/-- Assemble already checked prefixes without evaluating their arithmetic again. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (n : ℕ) (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hprefix : pairIndexedWitnessesPrefixBool a b r0 bound vertices n
      witnesses destinations = true)
    (htail : pairIndexedWitnessesCheckedBool a b r0 bound vertices
      (witnesses.drop n) (destinations.drop n) = true) :
    pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations = true :=
  (pairIndexedWitnessesCheckedBool_eq_prefix_drop a b r0 bound vertices n witnesses destinations).trans
    (Bool.and_eq_true_iff.mpr ⟨hprefix, htail⟩)





end D1Bound5
end
