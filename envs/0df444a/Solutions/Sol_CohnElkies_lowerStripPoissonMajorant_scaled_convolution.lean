-- Prove2me | solution 1 for CohnElkies.lowerStripPoissonMajorant_scaled_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/75911ff4-5346-4b17-add3-f580ff7a7eef

import Mathlib
import Definitions.Def_SpherePacking

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R σ s : ℝ) :
    lowerStripPoissonMajorant ℓ R σ s =
      ∫ Y : ℝ,
        stripPoissonKernel σ (s / ℓ - Y) *
          lowerGammaBoundaryLog ℓ R (ℓ * Y) := by
  let f : ℝ → ℝ := fun Y =>
    stripPoissonKernel σ (s / ℓ - Y) *
      lowerGammaBoundaryLog ℓ R (ℓ * Y)
  calc
    lowerStripPoissonMajorant ℓ R σ s =
        ∫ T : ℝ, f (s / ℓ - T) := by
      unfold lowerStripPoissonMajorant
      apply integral_congr_ae
      filter_upwards [] with T
      try dsimp [f]
      have harg : s / ℓ - (s / ℓ - T) = T := by
        ring
      rw [harg]
      congr 1
      field_simp [hℓ.ne']
    _ = ∫ Y : ℝ, f Y :=
      integral_sub_left_eq_self f volume (s / ℓ)
end CohnElkies
