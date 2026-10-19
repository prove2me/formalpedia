-- Prove2me | solution 2 for CohnElkies.harmonic_bottom_normalized_height_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:11.611067+00:00
-- url     : https://prove2.me/submissions/1d677357-6395-46ad-beb2-a99a1fa6505d

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) :
    Tendsto
      (fun z : ℂ => z.im / ℓ)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (-1 : ℝ)) := by
  have h := ((Complex.continuous_im.div_const ℓ).tendsto ((s : ℂ) - Complex.I * (ℓ : ℂ))).mono_left
    (nhdsWithin_le_nhds (s := Complex.im ⁻¹' Set.Ioo (-ℓ) ℓ))
  have hv : ((s : ℂ) - Complex.I * (ℓ : ℂ)).im / ℓ = -1 := by
    simp; field_simp
  rw [hv] at h
  exact h

