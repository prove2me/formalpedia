-- Prove2me | solution 1 for CohnElkies.eventually_saddleSmallResidueTruncation_double_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/d4744bc0-d175-4d11-a304-7cf009fffd50

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueTruncation_div

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ℓ : ℝ in atTop,
      2 * (saddleSmallResidueTruncation ℓ : ℝ) ≤ ℓ := by
  have hsmall :=
    tendsto_saddleSmallResidueTruncation_div.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall,
    eventually_gt_atTop (0 : ℝ)]
    with ℓ hratio hℓ
  have h := (div_lt_iff₀ hℓ).mp hratio
  linarith
end CohnElkies
