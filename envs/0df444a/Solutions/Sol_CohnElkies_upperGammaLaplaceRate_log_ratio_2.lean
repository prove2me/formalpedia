-- Prove2me | solution 2 for CohnElkies.upperGammaLaplaceRate_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:47:03.657325+00:00
-- url     : https://prove2.me/submissions/5d54e854-ff23-45ff-bc48-63f5c3d6e975

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
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
  congr 1
  have ha : 0 < η + 2 * (k : ℝ) / ℓ := by positivity
  have h2 : (0:ℝ) < ℓ / 2 := by positivity
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have e1 : ((ℓ * η / 2 : ℝ) : ℂ) + Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) + (k : ℂ) =
      ((ℓ / 2 : ℝ) : ℂ) * (((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) + Complex.I * (T : ℂ)) := by
    push_cast; field_simp; ring
  have e2 : ℓ * η / 2 + (k : ℝ) = ℓ / 2 * (η + 2 * (k : ℝ) / ℓ) := by field_simp
  rw [e1, e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2,
    mul_div_mul_left _ _ h2.ne']

