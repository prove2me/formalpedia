-- Prove2me | solution 2 for CohnElkies.harmonic_bottom_real_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:10.477534+00:00
-- url     : https://prove2.me/submissions/b990c69c-ff7d-4322-98df-298849ca4493

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology


theorem solution
    {ℓ : ℝ} (s : ℝ) :
    Tendsto Complex.re
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 s) := by
  have := (Complex.continuous_re.tendsto ((s : ℂ) - Complex.I * (ℓ : ℂ))).mono_left
    (nhdsWithin_le_nhds (s := Complex.im ⁻¹' Set.Ioo (-ℓ) ℓ))
  simpa using this

