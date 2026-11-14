-- Prove2me | solution 1 for ConsistentSubmodular.deterministicLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:49:01.555576+00:00
-- url     : https://prove2.me/submissions/1383f0a8-3999-43d4-8110-90050fcf7e9e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths
import Theorems.Thm_ConsistentSubmodular_certificateReduction
import Theorems.Thm_ConsistentSubmodular_threeQuarterCertificates

section

open ConsistentSubmodular

theorem solution : DeterministicLowerGoal := by
  obtain ⟨K, hK⟩ := certificateReduction 3
  refine ⟨K, fun ε hε hε1 => ?_⟩
  obtain ⟨R, hRK, hR⟩ := hK ε hε hε1
  exact ⟨R, hRK, hR (3 / 4) (by norm_num) le_rfl fun n W _ =>
    (threeQuarterCertificates n W).map fun Z =>
      Z.mono (show W.lastStage + 3 ≤ 3 * (W.lastStage + 1) by omega)⟩

end
