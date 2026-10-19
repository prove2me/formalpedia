-- Prove2me | solution 1 for CohnElkies.upperGammaVariance_firstBranch_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/dcfcefa2-a973-4e8b-9563-90612b5309cf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hscale : 1 ≤ ℓ * η) :
    η * upperGammaVariance ℓ η ≤ (3 / 2 : ℝ) := by
  have hone : 1 / (ℓ * η) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hℓ hη)).2
    simpa using! hscale
  calc
    η * upperGammaVariance ℓ η ≤
        η * (1 / (2 * η) + 1 / (ℓ * η ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (upperGammaVariance_bounds hℓ hη).2 hη.le
    _ = 1 / 2 + 1 / (ℓ * η) := by
      field_simp [hℓ.ne', hη.ne']
    _ ≤ (3 / 2 : ℝ) := by linarith
end CohnElkies
