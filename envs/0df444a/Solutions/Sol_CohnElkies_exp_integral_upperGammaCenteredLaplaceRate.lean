-- Prove2me | solution 1 for CohnElkies.exp_integral_upperGammaCenteredLaplaceRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/f6ea7f8d-0661-4a98-9da4-45dfdf6e1ffa

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaLaplaceRate_pos
import Theorems.Thm_CohnElkies_exp_integral_upperCenteredLaplaceKernel_scale

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (k : ℕ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a) =
      ((((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) /
        (((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
            (k : ℂ)))) *
        Complex.exp
          (-Complex.I *
            (((ℓ * T / 2 /
              (ℓ * η / 2 + (k : ℝ)) : ℝ) : ℂ))) := by
  have hs : 0 < ℓ / 2 := by positivity
  have hc := upperGammaLaplaceRate_pos hℓ hη k
  have hreal :
      ℓ / 2 * (η + 2 * (k : ℝ) / ℓ) =
        ℓ * η / 2 + (k : ℝ) := by
    field_simp [hℓ.ne']
  have himag : ℓ / 2 * T = ℓ * T / 2 := by
    ring
  have harg :
      (((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) -
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) =
        ((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
            (k : ℂ) := by
    push_cast
    ring
  have h :=
    exp_integral_upperCenteredLaplaceKernel_scale
      hc hs T
  rw [hreal, himag, harg] at h
  exact h
end CohnElkies
