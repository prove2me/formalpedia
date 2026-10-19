-- Prove2me | solution 1 for CohnElkies.positiveShellDamping_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/70607523-a11d-4baa-84e9-708b1b31881a

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
    {ε ℓ δ T : ℝ}
    (hℓ : 0 ≤ ℓ) :
    0 ≤ positiveShellDamping ε ℓ δ T := by
  unfold positiveShellDamping
  apply mul_nonneg hℓ
  apply intervalIntegral.integral_nonneg
    (show shellLocation ε ≤ shellLocation ε + 1 by linarith)
  intro a ha
  unfold positiveShellDensity
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le)
      (Real.cosh_pos _).le)
    (sub_nonneg.mpr (Real.cos_le_one _))
end CohnElkies
