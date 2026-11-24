-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.inv_dz_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:56.481627+00:00
-- url     : https://prove2.me/submissions/ec67dc48-a8e7-4565-b113-5a1cf598d735

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_cc_dz
import Theorems.Thm_Formalism_L2_Th1_B_Jets_ccX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_law_subst
import Theorems.Thm_Formalism_L2_Th1_B_Jets_cc_law
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_mul
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_subst
import Theorems.Thm_Formalism_L2_Th1_B_restrictSecondZero_inVar_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Jets
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)
variable {K : Type} [Field K] [CharZero K]
variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    (dz l)⁻¹ = ev0 (pd 1 F) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
    PowerSeries.constantCoeff_X
  have hz : MvPowerSeries.constantCoeff (0 : PowerSeries K) = 0 := map_zero _
  have hev : ev0 F = PowerSeries.X := by
    have hl := law_subst hF hc hX hz
    apply psubst_injective h0 h1 (cc_law hF hX hz) hX
    rw [hl,
      PowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]
  have hcob : PowerSeries.subst F l = at1 0 l + at1 1 l := by
    have e := hc
    simp only [cob] at e
    linear_combination e
  have hd := congrArg (MvPowerSeries.pderiv K 1) hcob
  simp only [at1] at hd
  rw [Formalism.G.LogCR.pderiv_psubst hF, map_add, Formalism.G.LogCR.pderiv_psubst (ccX (0 : Fin 2)),
    Formalism.G.LogCR.pderiv_psubst (ccX (1 : Fin 2)), MvPowerSeries.pderiv_X_of_ne (by decide),
    MvPowerSeries.pderiv_X_self, mul_zero, zero_add, mul_one] at hd
  have he := congrArg ev0 hd
  have w := restrictSecondZero_inVar_one (K := K) (dz l)
  have c1 := cc_dz h1
  simp only [at1, dz] at w c1
  rw [evalYZero_mul, evalYZero_subst _ hF, hev, w, c1, map_one] at he
  rw [PowerSeries.X_subst] at he
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_dz h1]; exact one_ne_zero)]
  simp only [pd, dz]
  rw [mul_comm]
  exact he
end Formalism.L2.Th1.B.Jets
