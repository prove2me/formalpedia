-- Prove2me | solution 1 for CohnElkies.saddleNegativeRelativeCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/4777836b-486d-4d87-882d-56fc02c4fddb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleNegativeFrequencyMass_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ saddleNegativeRelativeCoefficient ε := by
  unfold saddleNegativeRelativeCoefficient
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (by positivity))
        (Real.exp_pos _).le)
      (saddleNegativeFrequencyMass_nonneg ε))
    (mul_pos (by norm_num) (beta_pos hε)).le
end CohnElkies
