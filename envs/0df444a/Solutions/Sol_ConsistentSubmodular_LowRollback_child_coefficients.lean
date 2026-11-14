-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.child_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:36.68354+00:00
-- url     : https://prove2.me/submissions/528e4184-d86a-4bbe-9254-3cb54ef437cd

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions

section

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    14 ≤ cpoly q ∧ 0 ≤ apoly q ∧ apoly q ≤ 3 ∧ 0 < SA q := by
  have h1q : 0 ≤ 1 - q := by linarith
  have hc : 14 ≤ cpoly q := by
    have hi : cpoly q = 14 + 25 * (1 - q) + 8 * (1 - q) ^ 2 + (1 - q) ^ 3 := by unfold cpoly; ring
    rw [hi]
    have hcube := pow_nonneg h1q 3
    nlinarith [sq_nonneg (1 - q)]
  have ha : 0 ≤ apoly q := mul_nonneg hq0 (by linarith)
  have ha3 : apoly q ≤ 3 := by
    have hm := mul_nonneg h1q (show 0 ≤ 3 - q by linarith)
    unfold apoly
    nlinarith
  refine ⟨hc, ha, ha3, ?_⟩
  have hn : 0 ≤ npoly q := mul_nonneg (by linarith) (sq_nonneg _)
  unfold SA
  linarith

end
