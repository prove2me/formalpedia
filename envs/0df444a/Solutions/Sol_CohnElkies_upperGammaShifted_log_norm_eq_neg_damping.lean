-- Prove2me | solution 1 for CohnElkies.upperGammaShifted_log_norm_eq_neg_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/de993b97-4de5-400f-9e90-09f39a919517

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaPositiveShifted_log_norm_eq_neg_damping

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Real.log
        (‖Complex.Gamma
            (((ℓ * η / 2 : ℝ) : ℂ) -
              Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ /
          Real.Gamma (ℓ * η / 2)) =
      -upperGammaDamping ℓ η T := by
  have hconj :
      ‖Complex.Gamma
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ =
      ‖Complex.Gamma
          (((ℓ * η / 2 : ℝ) : ℂ) +
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ := by
    have harg (m b : ℝ) :
        starRingEnd ℂ
          ((m : ℂ) + Complex.I * (b : ℂ)) =
          ((m : ℂ) - Complex.I * (b : ℂ)) := by
      simp [sub_eq_add_neg]
    rw [← harg (ℓ * η / 2) (ℓ * T / 2),
      Complex.Gamma_conj,
      Complex.norm_conj]
  rw [hconj]
  exact upperGammaPositiveShifted_log_norm_eq_neg_damping
    hℓ hη T
end CohnElkies
