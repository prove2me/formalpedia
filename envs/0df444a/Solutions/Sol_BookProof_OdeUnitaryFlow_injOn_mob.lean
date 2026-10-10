-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.injOn_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:12.337357+00:00
-- url     : https://prove2.me/submissions/a80356ad-7a12-487b-a87b-541894aeee5a

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.injOn_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_mob_neg_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : InjOn (mob t) (flowDom t) := by

  intro a ha b hb hab
  have ha' := mob_neg_mob t a ha
  have hb' := mob_neg_mob t b hb
  rw [← ha', ← hb', hab]
