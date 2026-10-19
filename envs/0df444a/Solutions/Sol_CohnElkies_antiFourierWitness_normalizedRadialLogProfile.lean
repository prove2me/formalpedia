-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedRadialLogProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/6c570418-2e4a-4480-b173-c80995a0795c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_integrable
import Theorems.Thm_CohnElkies_integral_abs_normalizedRadialLogProfile
import Theorems.Thm_CohnElkies_integral_normalizedRadialLogProfile_eq_zero_of_antiFourier
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_nonneg_of_exterior

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    let φ := normalizedRadialLogProfile hd w.function R
    Integrable φ ∧
      (∫ v : ℝ, φ v) = 0 ∧
      (∫ v : ℝ, |φ v|) = 1 ∧
      (∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) := by
  try dsimp
  refine ⟨normalizedRadialLogProfile_integrable
      hd w.function w.radial hR, ?_, ?_, ?_⟩
  · exact integral_normalizedRadialLogProfile_eq_zero_of_antiFourier
      hd w.function w.radial w.anti_fourier w.zero_value hR
  · exact integral_abs_normalizedRadialLogProfile hd w.function
      w.radial w.real w.nonzero hR
  · intro v hv
    exact normalizedRadialLogProfile_nonneg_of_exterior
      hd w.function w.nonzero hR w.eventually_nonneg v hv
end CohnElkies
