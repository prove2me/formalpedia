-- Prove2me | solution 1 for Eden.divergence_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:16.075806+00:00
-- url     : https://prove2.me/submissions/a7881955-5cfc-4910-b05b-0d0545e47125

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
import Theorems.Thm_Eden_divergence_eq_rates
import Theorems.Thm_Eden_total_rate_le


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) : divergence c p ≤ 4 - c := by
  rw [divergence_eq_rates]
  exact total_rate_le _ _ _
end Eden
