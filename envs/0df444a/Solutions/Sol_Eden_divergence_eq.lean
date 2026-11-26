-- Prove2me | solution 1 for Eden.divergence_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:50.627898+00:00
-- url     : https://prove2.me/submissions/c29f2c2b-cb79-43e3-a5bc-fb478b59967b

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
import Theorems.Thm_Eden_divergence_eq_rates
import Theorems.Thm_Eden_total_rate_identity


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 - 6 * (radiusSq₂ p - 1) ^ 2 := by
  rw [divergence_eq_rates]
  exact total_rate_identity _ _ _
end Eden
