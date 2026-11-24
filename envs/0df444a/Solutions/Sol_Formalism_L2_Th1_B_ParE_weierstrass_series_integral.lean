-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParE.weierstrass_series_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:20.135857+00:00
-- url     : https://prove2.me/submissions/a3c578c3-8864-4328-ac11-ca6eb86dd8c9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_P2M_Formalism_L2_Th1_B_ParE_integral_add__f399c0a1f89a
import Theorems.Thm_P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
namespace Formalism.L2.Th1.B.ParE
theorem _root_.solution : WIntegral := by
  intro K _ _ _ c0 e1 P l i ep F hLL hCH hce
  obtain ⟨hepI, hep1, hcurve, -⟩ := hCH
  have hl0 : PowerSeries.constantCoeff l = 0 := hLL.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hLL.2.2.2.1
  have ha : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero hl0
  have hlne : l ≠ 0 := by
    rintro rfl
    simp at hl1
  have hD0c : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2 : PowerSeries K) ≠ 0 := by
    simp
  have hCe : PowerSeries.subst l (PowerSeries.C e1 : PowerSeries K) = (PowerSeries.C e1 : PowerSeries K) := by
    have h := (PowerSeries.substAlgHom ha).commutes e1
    rw [PowerSeries.coe_substAlgHom] at h
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using h
  have hw : wOf e1 P * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD0c, mul_one]
  have hWD : PowerSeries.subst l (wOf e1 P) *
      (1 + l ^ 2 * PowerSeries.subst l P - PowerSeries.C e1 * l ^ 2) = l ^ 2 := by
    have h := congrArg (PowerSeries.subst l) hw
    rw [← PowerSeries.coe_substAlgHom ha] at h
    simp only [map_add, map_sub, map_one, map_mul, map_pow] at h
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_X ha, hCe] at h
    exact h
  have hkey : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * l ^ 2 := by
    rw [map_sub]
    linear_combination (-PowerSeries.subst l (wOf e1 P)) * hcurve + PowerSeries.X ^ 2 * hWD
  have h1 : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hlne) hkey
  refine ⟨h1, ?_⟩
  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hEI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) :=
    integral_add' hepI (integral_mul' (integral_C' hce) hX2)
  have hEc : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2 : PowerSeries K) = 1 := by
    have h : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
      simp [hep1]
    exact h
  have hEc' : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ≠ 0 := by
    simp [hep1]
  have hVI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ :=
    integral_of_mul_eq_one hEI hEc (PowerSeries.inv_mul_cancel _ hEc')
  have hWe : PowerSeries.subst l (wOf e1 P) =
      PowerSeries.X ^ 2 * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
    calc PowerSeries.subst l (wOf e1 P)
        = PowerSeries.subst l (wOf e1 P) * ((ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hEc', mul_one]
      _ = (PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [h1]
  rw [hWe]
  exact integral_mul' hX2 hVI
end Formalism.L2.Th1.B.ParE
