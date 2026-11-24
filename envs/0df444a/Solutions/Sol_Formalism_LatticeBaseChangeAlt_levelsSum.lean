-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.levelsSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:25.723788+00:00
-- url     : https://prove2.me/submissions/3c4a9f01-1703-40ce-bf8e-69cfe1c90495

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_BCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Finset
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LevelsSum := by
  intro ι _ ep f mm v T c' h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hf : (0 : ℝ) ≤ (f z : ℝ) := Nat.cast_nonneg _
  calc (mm z : ℝ) * f z ≤ (ep z * T * c' * v z) * f z := mul_le_mul_of_nonneg_right (h z) hf
    _ = T * c' * ((ep z : ℝ) * f z * v z) := by ring
end Formalism.LatticeBaseChangeAlt
