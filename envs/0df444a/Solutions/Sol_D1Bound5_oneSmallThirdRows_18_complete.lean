-- Prove2me | solution 1 for D1Bound5.oneSmallThirdRows_18_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:08.520166+00:00
-- url     : https://prove2.me/submissions/7611472a-7dcf-4784-94d1-1f87aa944487

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
import Theorems.Thm_D1Bound5_oneSmallThirds_18_complete

section
namespace D1Bound5
open QuadInt



















































theorem _root_.solution :
    OneSmallThirdRowProperty oneSmallPairA_18 oneSmallPairB_18 := by
  intro s hbound horder ha hb hpair
  have hm := oneSmallThirds_18_complete s hbound horder ha hb hpair
  simp only [oneSmallThirds_18, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  · exact Or.inr ⟨7943, by unfold OneSmallRowMembership; decide +kernel⟩











































end D1Bound5
end
