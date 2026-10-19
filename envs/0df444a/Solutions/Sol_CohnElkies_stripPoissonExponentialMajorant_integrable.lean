-- Prove2me | solution 1 for CohnElkies.stripPoissonExponentialMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/758f8123-807e-4764-b4b9-cac325534db2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_exp_neg_mul_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable stripPoissonExponentialMajorant := by
  exact
    (integrable_exp_neg_mul_abs
      (half_pos Real.pi_pos)).const_mul (Real.pi / 2)
end CohnElkies
