-- Prove2me | solution 1 for CohnElkies.upperGammaLaplaceRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/4f7ce710-eb06-409a-8df5-c4fe252fb5e9

import Mathlib
import Definitions.Def_SpherePacking

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (k : ℕ) :
    0 < η + 2 * (k : ℝ) / ℓ := by
  exact add_pos_of_pos_of_nonneg hη
    (div_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hℓ.le)
end CohnElkies
