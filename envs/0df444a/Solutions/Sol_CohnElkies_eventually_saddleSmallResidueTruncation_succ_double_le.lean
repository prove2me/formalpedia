-- Prove2me | solution 1 for CohnElkies.eventually_saddleSmallResidueTruncation_succ_double_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/1772023f-f80b-4da9-bf28-c8a295716104

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
      2 * ((saddleSmallResidueTruncation ℓ + 1 : ℕ) : ℝ) ≤ ℓ := by
  have hsmall :=
    tendsto_saddleSmallResidueTruncation_div.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall,
    eventually_ge_atTop (4 : ℝ)]
    with ℓ hratio hℓ
  have hℓpos : 0 < ℓ := by linarith
  have h := (div_lt_iff₀ hℓpos).mp hratio
  push_cast
  linarith
end CohnElkies
