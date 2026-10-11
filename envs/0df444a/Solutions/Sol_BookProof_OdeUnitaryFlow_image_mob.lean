-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.image_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:58:15.737676+00:00
-- url     : https://prove2.me/submissions/0a91e678-afda-4ff2-bcf3-0688f4ba83bf

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.image_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_mob_mem_flowDom_neg
import Theorems.Thm_BookProof_OdeUnitaryFlow_mob_neg_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : mob t '' flowDom t = flowDom (-t) := by

  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact mob_mem_flowDom_neg t x hx
  · intro y hy
    refine ⟨mob (-t) y, ?_, ?_⟩
    · have h := mob_mem_flowDom_neg (-t) y hy
      simpa using h
    · have h := mob_neg_mob (-t) y hy
      simpa using h
