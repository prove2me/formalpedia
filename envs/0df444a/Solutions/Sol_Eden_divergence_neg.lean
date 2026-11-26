-- Prove2me | solution 1 for Eden.divergence_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:34.290777+00:00
-- url     : https://prove2.me/submissions/343fa237-3987-4d0f-992c-6f718bcff857

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
import Theorems.Thm_Eden_divergence_le

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (p : PhaseSpace) : divergence c p < 0 := by
  linarith [divergence_le c p]
end Eden
