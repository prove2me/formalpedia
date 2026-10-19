-- Prove2me | solution 1 for CohnElkies.no_antiFourierWitness_of_fourierInversion_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/2ba96d4e-5eec-47d8-b734-d3e44d714520

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedRadialLogProfile
import Theorems.Thm_CohnElkies_no_normalizedProfile_of_fourierInversion_lt_half

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
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (normalizedRadialLogProfile hd w.function R v : ℂ) =
        (Real.exp (a * v) : ℂ) *
          ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v))
    (hsmall : ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a <
      (1 / 2 : ℝ)) : False := by
  obtain ⟨hintegrable, hmean, hmass, hsign⟩ :=
    antiFourierWitness_normalizedRadialLogProfile hd hR w
  exact no_normalizedProfile_of_fourierInversion_lt_half
    hintegrable hmean hmass hsign ha Z hinversion hsmall
end CohnElkies
