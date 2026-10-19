-- Prove2me | solution 1 for CohnElkies.upperGammaMeasureDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/044903e6-11fd-432a-9013-4ce298e8dc7e

import Mathlib
import Definitions.Def_SpherePacking

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
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    0 < upperGammaMeasureDensity ℓ η a := by
  have hx : 0 < 2 * a / ℓ := by positivity
  have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have he := Real.exp_lt_one_iff.mpr (show -(2 * a / ℓ) < 0 by linarith)
    linarith
  unfold upperGammaMeasureDensity
  exact div_pos (Real.exp_pos _) (mul_pos ha hden)
end CohnElkies
