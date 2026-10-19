-- Prove2me | solution 1 for CohnElkies.upperGammaLaplaceRate_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/a8347a75-78f2-4fec-a4d5-405938838edf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaLaplaceRate_pos
import Theorems.Thm_CohnElkies_upperComplex_norm_ratio_scale

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
    Real.log
        (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
            Complex.I * (T : ℂ)‖ /
          (η + 2 * (k : ℝ) / ℓ)) =
      Real.log
        (‖((ℓ * η / 2 : ℝ) : ℂ) +
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
              (k : ℂ)‖ /
          (ℓ * η / 2 + (k : ℝ))) := by
  have hs : 0 < ℓ / 2 := by positivity
  have hc := upperGammaLaplaceRate_pos hℓ hη k
  have hreal :
      ℓ / 2 * (η + 2 * (k : ℝ) / ℓ) =
        ℓ * η / 2 + (k : ℝ) := by
    field_simp [hℓ.ne']
  have himag : ℓ / 2 * T = ℓ * T / 2 := by
    ring
  have harg :
      (((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) +
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) =
        ((ℓ * η / 2 : ℝ) : ℂ) +
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
            (k : ℂ) := by
    push_cast
    ring
  have hscale := upperComplex_norm_ratio_scale
    (s := ℓ / 2)
    (c := η + 2 * (k : ℝ) / ℓ) hs hc T
  rw [hreal, himag, harg] at hscale
  exact congrArg Real.log hscale.symm
end CohnElkies
