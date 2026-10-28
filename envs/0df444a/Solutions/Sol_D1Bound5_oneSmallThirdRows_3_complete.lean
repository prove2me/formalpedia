-- Prove2me | solution 1 for D1Bound5.oneSmallThirdRows_3_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:34.922014+00:00
-- url     : https://prove2.me/submissions/d0a25916-87db-4e3e-bc99-b7583982bfa1

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
import Theorems.Thm_D1Bound5_oneSmallThirds_3_complete

section
namespace D1Bound5
open QuadInt





















theorem _root_.solution :
    OneSmallThirdRowProperty oneSmallPairA_3 oneSmallPairB_3 := by
  intro s hbound horder ha hb hpair
  have hm := oneSmallThirds_3_complete s hbound horder ha hb hpair
  simp only [oneSmallThirds_3, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  · exact Or.inr ⟨3896, by unfold OneSmallRowMembership; decide +kernel⟩









































































end D1Bound5
end
