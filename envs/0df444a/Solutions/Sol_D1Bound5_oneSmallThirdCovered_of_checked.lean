-- Prove2me | solution 1 for D1Bound5.oneSmallThirdCovered_of_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:10.256002+00:00
-- url     : https://prove2.me/submissions/027ec77c-e041-4bb4-944c-489303623c0a

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff

section
namespace D1Bound5
open QuadInt

















theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b : QuadInt tau nu)
    (diskEntries allowed : List (QuadInt tau nu))
    (hcover : ∀ s ∈ disk tau nu 224, s ∈ diskEntries)
    (hcheck : oneSmallThirdCoveredBool a b diskEntries allowed = true)
    (s : QuadInt tau nu) (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) : s ∈ allowed := by
  have hm := hcover s ((mem_disk_iff hd 224 s).2 hbound)
  have hc := List.all_eq_true.mp hcheck s hm
  have hra := (hasSquareRoot_iff hd _).2 hpair.1
  have hrb := (hasSquareRoot_iff hd _).2 hpair.2
  simpa [horder, ha, hb, hra, hrb] using hc





end D1Bound5
end
