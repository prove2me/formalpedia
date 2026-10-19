-- Prove2me | solution 1 for CohnElkies.normalizedProfile_negativeHalfline_mass_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/a9166892-92dc-40aa-a151-892c2ac3b627

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_profileNegativePart_integrable
import Theorems.Thm_CohnElkies_integral_profileNegativePart_eq_half
import Theorems.Thm_CohnElkies_profileNegativePart_setIntegral_Iic_eq_integral

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (1 / 2 : ℝ) ≤ ∫ v in Iic (0 : ℝ), |φ v| := by
  have hneg := profileNegativePart_integrable hφ
  calc
    (1 / 2 : ℝ) = ∫ v : ℝ, profileNegativePart φ v :=
      (integral_profileNegativePart_eq_half hφ hmean hmass).symm
    _ = ∫ v in Iic (0 : ℝ), profileNegativePart φ v :=
      (profileNegativePart_setIntegral_Iic_eq_integral hsign).symm
    _ ≤ ∫ v in Iic (0 : ℝ), |φ v| := by
      refine setIntegral_mono_on hneg.integrableOn hφ.abs.integrableOn
        measurableSet_Iic ?_
      intro v _
      unfold profileNegativePart
      exact max_le (neg_le_abs _) (abs_nonneg _)
end CohnElkies
