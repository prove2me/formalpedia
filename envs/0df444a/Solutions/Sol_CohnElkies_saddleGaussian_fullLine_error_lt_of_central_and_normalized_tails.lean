-- Prove2me | solution 1 for CohnElkies.saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/5a53571c-7644-41e8-94c2-c457ca94c923

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussian_fullLine_error_le_central_add_tails
import Theorems.Thm_CohnElkies_saddleSource_scaled_tail_lt_relative_gaussian

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u R A κcentral κsource κgaussian : ℝ}
    {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hcentral :
      ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ <
        κcentral * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T))
    (hsource :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) <
          κsource * A)
    (hgaussian :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) <
          κgaussian * A) :
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ <
      (κcentral + (κsource + κgaussian) /
        Real.sqrt (2 * Real.pi)) * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hsplit := saddleGaussian_fullLine_error_le_central_add_tails
    hF hG R
  have hone : (0 : ℝ) < 1 := by norm_num
  have hsource' :=
    saddleSource_scaled_tail_lt_relative_gaussian
      (ε := ε) (u := u) (C := (1 : ℝ)) (A := (1 : ℝ))
      (κ := κsource * A)
      (X := ∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖)
      (W := ∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖)
      hℓ hV hone hone (by simp) hsource
  have hgaussian' :=
    saddleSource_scaled_tail_lt_relative_gaussian
      (ε := ε) (u := u) (C := (1 : ℝ)) (A := (1 : ℝ))
      (κ := κgaussian * A)
      (X := ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖)
      (W := ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖)
      hℓ hV hone hone (by simp) hgaussian
  calc
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ ≤
        ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
          (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
          (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := hsplit
    _ < (κcentral * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) +
        ((κsource * A /
            Real.sqrt (2 * Real.pi)) *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) +
        ((κgaussian * A /
            Real.sqrt (2 * Real.pi)) *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) := by
      simpa using! add_lt_add (add_lt_add hcentral hsource') hgaussian'
    _ = (κcentral + (κsource + κgaussian) /
        Real.sqrt (2 * Real.pi)) * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
      ring
end CohnElkies
