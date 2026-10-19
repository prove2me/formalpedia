-- Prove2me | solution 1 for CohnElkies.no_normalizedProfile_of_fourierInversion_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/548ae759-68c5-4da8-8807-7620cdc13343

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedProfile_negativeHalfline_mass_ge_half
import Theorems.Thm_CohnElkies_negativeHalfline_le_of_fourierInversion

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (φ v : ℂ) = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v))
    (hsmall : ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a <
      (1 / 2 : ℝ)) : False := by
  have hlower := normalizedProfile_negativeHalfline_mass_ge_half
    hφ hmean hmass hsign
  have hupper := negativeHalfline_le_of_fourierInversion
    hφ ha Z hinversion
  linarith
end CohnElkies
