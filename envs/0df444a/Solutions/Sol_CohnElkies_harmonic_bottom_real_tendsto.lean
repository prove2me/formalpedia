-- Prove2me | solution 1 for CohnElkies.harmonic_bottom_real_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/7265ebd9-c6a5-4f40-8fcd-512d2d3b5826

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
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (s : ℝ) :
    Tendsto Complex.re
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 s) := by
  convert! Complex.continuous_re.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds using 1;
      simp
end CohnElkies
