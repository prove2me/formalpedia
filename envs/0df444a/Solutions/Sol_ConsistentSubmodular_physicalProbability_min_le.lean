-- Prove2me | solution 1 for ConsistentSubmodular.physicalProbability_min_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:17.198522+00:00
-- url     : https://prove2.me/submissions/4a02f4a2-7fc7-4a7a-990d-47043d2bbb36

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap

section

open scoped BigOperators
open ConsistentSubmodular
variable {n m : ℕ}

theorem solution
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m) (e : Fin n) :
    physicalProbability cores (fun i => min (p i) (q i)) e ≤
      min (physicalProbability cores p e) (physicalProbability cores q e) := by
  apply le_min
  · apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact min_le_left _ _
    · rfl
  · apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact min_le_right _ _
    · rfl

end
