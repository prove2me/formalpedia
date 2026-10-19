-- Prove2me | solution 2 for CohnElkies.normalizedProfile_negativeHalfline_le_of_exp_majorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:03:25.631038+00:00
-- url     : https://prove2.me/submissions/a9422a6a-e096-4ade-b250-d35220a383ed

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


theorem solution
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a B : ℝ} (ha : 0 < a)
    (hbound : ∀ v : ℝ, v ≤ 0 → |φ v| ≤ B * Real.exp (a * v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤ B / a := by
  have hexp : IntegrableOn (fun v : ℝ => B * Real.exp (a * v)) (Iic 0) :=
    (integrableOn_exp_mul_Iic ha 0).const_mul B
  calc (∫ v in Iic (0 : ℝ), |φ v|) ≤ ∫ v in Iic (0 : ℝ), B * Real.exp (a * v) :=
        setIntegral_mono_on hφ.abs.integrableOn hexp measurableSet_Iic hbound
    _ = B / a := by
        rw [integral_const_mul, integral_exp_mul_Iic ha 0]
        simp [div_eq_mul_inv]

