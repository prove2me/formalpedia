-- Prove2me | solution 1 for D1Bound5.pairGraphTriangleFreeBool_of_split
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:39:03.283979+00:00
-- url     : https://prove2.me/submissions/31c6f8f1-54ec-4a59-8868-12a8f6962fc5

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
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_independent_cover
import Theorems.Thm_D1Bound5_pairSplitByMask_covers

section
namespace D1Bound5
open QuadInt











theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu)) (colors : ℕ)
    (hleft : pairIndependentBool sieve (pairSplitByMask vertices colors).1 = true)
    (hright : pairIndependentBool sieve (pairSplitByMask vertices colors).2 = true) :
    pairGraphTriangleFreeBool sieve vertices = true := by
  apply pairGraphTriangleFreeBool_of_independent_cover sieve vertices
    (pairSplitByMask vertices colors).1 (pairSplitByMask vertices colors).2
    (fun z hz => pairSplitByMask_covers vertices colors z hz) hleft hright

end D1Bound5
end
