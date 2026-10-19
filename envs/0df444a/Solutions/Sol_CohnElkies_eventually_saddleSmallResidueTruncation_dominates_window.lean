-- Prove2me | solution 1 for CohnElkies.eventually_saddleSmallResidueTruncation_dominates_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/0d62fb2b-09a9-4fb2-a4fe-1f6efe5ab231

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallResidueTruncation_lower

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          2 * y ≤
            (saddleSmallResidueTruncation ℓ : ℝ) + 2 := by
  filter_upwards
    [Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max C 0))] with ℓ hlog
  intro y hy hyupper
  have hlogC : C ≤ Real.log ℓ := by
    simpa [max_eq_left hC] using! hlog
  have hN := saddleSmallResidueTruncation_lower ℓ
  nlinarith [hlogC]
end CohnElkies
