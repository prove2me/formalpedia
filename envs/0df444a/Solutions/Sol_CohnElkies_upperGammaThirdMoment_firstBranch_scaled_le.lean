-- Prove2me | solution 1 for CohnElkies.upperGammaThirdMoment_firstBranch_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/4b9c18e5-c505-4bf1-8a8b-33464f8f2060

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaThirdMoment_bounds

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
    η ^ 2 * upperGammaThirdMoment ℓ η ≤ (5 / 2 : ℝ) := by
  have hone : 1 / (ℓ * η) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hℓ hη)).2
    simpa using! hscale
  have htwo : 2 / (ℓ * η) ≤ (2 : ℝ) := by
    calc
      2 / (ℓ * η) = 2 * (1 / (ℓ * η)) := by ring
      _ ≤ 2 * (1 : ℝ) := by gcongr
      _ = 2 := by ring
  calc
    η ^ 2 * upperGammaThirdMoment ℓ η ≤
        η ^ 2 *
          (1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3)) :=
      mul_le_mul_of_nonneg_left
        (upperGammaThirdMoment_bounds hℓ hη).2
        (sq_nonneg η)
    _ = 1 / 2 + 2 / (ℓ * η) := by
      field_simp [hℓ.ne', hη.ne']
    _ ≤ (5 / 2 : ℝ) := by linarith
end CohnElkies
