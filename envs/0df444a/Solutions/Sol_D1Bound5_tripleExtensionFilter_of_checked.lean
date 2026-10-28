-- Prove2me | solution 1 for D1Bound5.tripleExtensionFilter_of_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:36.736223+00:00
-- url     : https://prove2.me/submissions/002e00aa-51f9-4b48-9f63-23696001f451

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff

section
namespace D1Bound5
open QuadInt

































theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b c : QuadInt tau nu)
    (vertices allowed : List (QuadInt tau nu))
    (hcheck : tripleExtensionFilterBool a b c vertices allowed = true)
    {z : QuadInt tau nu} (hz : z ∈ vertices)
    (h0 : z ≠ 0) (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c)
    (hs : ∃ r, r*r = c*z+1) : z ∈ allowed := by
  have h := List.all_eq_true.mp hcheck z hz
  have hs' := (hasSquareRoot_iff hd _).2 hs
  simpa [h0, ha, hb, hc, hs'] using h

end D1Bound5
end
