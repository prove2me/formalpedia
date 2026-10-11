-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.image_invMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:59:18.387899+00:00
-- url     : https://prove2.me/submissions/32d68fce-23de-4e72-bee0-b4f0810b83fb

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.image_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_invMap_invMap
import Theorems.Thm_BookProof_OdeUnitaryFlow_invMap_ne_zero
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution : invMap '' {x : ℝ | x ≠ 0} = {x : ℝ | x ≠ 0} := by

  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact invMap_ne_zero hx
  · intro y hy
    exact ⟨invMap y, invMap_ne_zero hy, invMap_invMap hy⟩
