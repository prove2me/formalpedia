-- Prove2me | solution 1 for CohnElkies.upperShortMargin_mul_exp_le_zero_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/fbd62efd-75c2-4731-9bd5-7bc0b44a8f76

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperShortMargin_mul_exp_antitone

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
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) :
    shortMargin ε a * Real.exp (ε * a) ≤
      1 - 10 * ε := by
  have h := upperShortMargin_mul_exp_antitone hε
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show a ∈ Ici 0 from ha) ha
  simpa [shortMargin] using! h
end CohnElkies
