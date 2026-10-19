-- Prove2me | solution 1 for CohnElkies.upperGammaShifted_modulus_eq_exp_neg_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/26a37300-7580-4d17-bc9e-c3ec203c8198

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaShifted_log_norm_eq_neg_damping

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
    ‖Complex.Gamma
        (((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ =
      Real.Gamma (ℓ * η / 2) *
        Real.exp (-upperGammaDamping ℓ η T) := by
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hΓ : 0 < Real.Gamma m :=
    Real.Gamma_pos_of_pos hm
  have hz :
      Complex.Gamma
          ((m : ℂ) - Complex.I * (b : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simpa using! hm
  have hratio :
      0 < ‖Complex.Gamma
          ((m : ℂ) - Complex.I * (b : ℂ))‖ /
            Real.Gamma m :=
    div_pos (norm_pos_iff.mpr hz) hΓ
  have hlog :=
    upperGammaShifted_log_norm_eq_neg_damping hℓ hη T
  change Real.log
    (‖Complex.Gamma
        ((m : ℂ) - Complex.I * (b : ℂ))‖ /
      Real.Gamma m) = -upperGammaDamping ℓ η T at hlog
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_log hratio] at hexp
  change ‖Complex.Gamma
      ((m : ℂ) - Complex.I * (b : ℂ))‖ =
        Real.Gamma m *
          Real.exp (-upperGammaDamping ℓ η T)
  calc
    ‖Complex.Gamma
        ((m : ℂ) - Complex.I * (b : ℂ))‖ =
        (‖Complex.Gamma
            ((m : ℂ) - Complex.I * (b : ℂ))‖ /
          Real.Gamma m) * Real.Gamma m := by
      rw [div_mul_cancel₀ _ hΓ.ne']
    _ = Real.exp (-upperGammaDamping ℓ η T) *
        Real.Gamma m := by
      rw [hexp]
    _ = Real.Gamma m *
        Real.exp (-upperGammaDamping ℓ η T) := by
      ring
end CohnElkies
