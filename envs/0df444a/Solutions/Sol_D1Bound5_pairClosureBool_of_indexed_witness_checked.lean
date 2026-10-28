-- Prove2me | solution 1 for D1Bound5.pairClosureBool_of_indexed_witness_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:34.200122+00:00
-- url     : https://prove2.me/submissions/5dea8d87-87e7-4f22-a5c7-6f1a5c2d6120

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_pairClosureBool_of_witness_checked
import Theorems.Thm_D1Bound5_pairClosureWitnessBool_of_indexed_checked

section
namespace D1Bound5
open QuadInt

















/-- The final closure assertion is unchanged. All canonical-root and sign
coverage is inherited from the accepted symbolic witness soundness theorem. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hcheck : pairClosureIndexedWitnessBool a b r0 bound vertices witnesses destinations = true) :
    pairClosureBool a b bound vertices = true :=
  pairClosureBool_of_witness_checked hd a b r0 bound vertices witnesses
    (pairClosureWitnessBool_of_indexed_checked a b r0 bound vertices witnesses
      destinations hcheck)

end D1Bound5
end
