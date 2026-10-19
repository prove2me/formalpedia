-- Prove2me | solution 1 for CohnElkies.normalizedProfile_negativeHalfline_le_of_exp_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/22269ea5-9253-4b9f-a8ea-338e51dbfe45

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
namespace CohnElkies
theorem _root_.solution
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a B : ℝ} (ha : 0 < a)
    (hbound : ∀ v : ℝ, v ≤ 0 → |φ v| ≤ B * Real.exp (a * v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤ B / a := by
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (a * v))
      (Iic (0 : ℝ)) := integrableOn_exp_mul_Iic ha 0
  have hmajorant :
      IntegrableOn (fun v : ℝ => B * Real.exp (a * v))
        (Iic (0 : ℝ)) := hexp.const_mul B
  calc
    (∫ v in Iic (0 : ℝ), |φ v|) ≤
        ∫ v in Iic (0 : ℝ), B * Real.exp (a * v) := by
      exact setIntegral_mono_on hφ.abs.integrableOn hmajorant
        measurableSet_Iic (fun v hv => hbound v hv)
    _ = B / a := by
      rw [integral_const_mul, integral_exp_mul_Iic ha 0]
      simp [div_eq_mul_inv]
end CohnElkies
