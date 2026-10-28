-- Prove2me | solution 1 for D1Bound5.pairClosureWitnessBool_of_indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:24:24.235438+00:00
-- url     : https://prove2.me/submissions/b0e686a5-75d9-4016-866a-9d75cd84223c

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
import Theorems.Thm_D1Bound5_pairRootWitnesses_all_of_indexed_checked

section
namespace D1Bound5
open QuadInt















/-- The indexed certificate proves the exact accepted witness certificate. -/
theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hcheck : pairClosureIndexedWitnessBool a b r0 bound vertices witnesses destinations = true) :
    pairClosureWitnessBool a b r0 bound vertices witnesses = true := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  exact Bool.and_eq_true_iff.mpr
    ⟨hparts.1, pairRootWitnesses_all_of_indexed_checked a b r0 bound vertices
      witnesses destinations hparts.2⟩



end D1Bound5
end
