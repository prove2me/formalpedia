-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/97082b6a-ce29-41c7-8831-c5ee6f5efac2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_antitoneOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    (d : ℕ) (c D n : ℝ) :
    AntitoneOn (lowerGammaScaledCappedClipped d c D n)
      (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hℓ : 0 ≤ (d : ℝ) / 2 := by positivity
  have hgamma :=
    lowerGammaBoundaryCapped_dimension_antitoneOn
      (d := d) (c * Real.sqrt d) D
      (show ((d : ℝ) / 2) * x ∈ Ici (0 : ℝ) from
        mul_nonneg hℓ hx)
      (show ((d : ℝ) / 2) * y ∈ Ici (0 : ℝ) from
        mul_nonneg hℓ hy)
      (mul_le_mul_of_nonneg_left hxy hℓ)
  unfold lowerGammaScaledCappedClipped
  exact max_le_max (by linarith) (le_refl (0 : ℝ))
end CohnElkies
