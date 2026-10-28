-- Prove2me | solution 1 for D1Bound5.oneSmallThirdRows_15_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:24.398707+00:00
-- url     : https://prove2.me/submissions/8bf6602a-1d20-4657-8bfd-8840816ecd88

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_oneSmallThirds_15_complete

section
namespace D1Bound5
open QuadInt













































theorem _root_.solution :
    OneSmallThirdRowProperty oneSmallPairA_15 oneSmallPairB_15 := by
  intro s hbound horder ha hb hpair
  have hm := oneSmallThirds_15_complete s hbound horder ha hb hpair
  simp only [oneSmallThirds_15, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  · exact Or.inr ⟨1760, by unfold OneSmallRowMembership; decide +kernel⟩

















































end D1Bound5
end
