-- Prove2me | solution 1 for CohnElkies.harmonic_bottom_normalized_height_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/cb6fd578-05d3-4e5e-9b2d-891a7b5ef5a9

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) :
    Tendsto
      (fun z : ℂ => z.im / ℓ)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (-1 : ℝ)) := by
  have hcontinuous : Continuous
      (fun z : ℂ => z.im / ℓ) := by
    fun_prop
  convert! hcontinuous.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds using 1;
      simp [hℓ.ne']
end CohnElkies
