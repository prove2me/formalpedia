-- Prove2me | solution 2 for CohnElkies.normalizedProfile_negativeHalfline_mass_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:21.361594+00:00
-- url     : https://prove2.me/submissions/3c29e36c-82eb-47df-9b79-4cca44eb73e6

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (1 / 2 : ℝ) ≤ ∫ v in Iic (0 : ℝ), |φ v| := by
  have hA := integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hφ.abs
  have hB := integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hφ
  have hP : ∫ v in (Iic (0:ℝ))ᶜ, |φ v| = ∫ v in (Iic (0:ℝ))ᶜ, φ v := by
    refine setIntegral_congr_fun measurableSet_Iic.compl (fun v hv => ?_)
    have : (0:ℝ) < v := by simpa using hv
    exact abs_of_nonneg (hsign v this.le)
  have hN : |∫ v in Iic (0:ℝ), φ v| ≤ ∫ v in Iic (0:ℝ), |φ v| := abs_integral_le_integral_abs
  have := neg_abs_le (∫ v in Iic (0:ℝ), φ v)
  linarith

