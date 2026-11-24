-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.invariant_derivation_subst_law_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:01.266634+00:00
-- url     : https://prove2.me/submissions/f19deb58-7c76-4342-b361-38df7c91e701

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_ccX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_Dj_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_Jets_law_subst
import Theorems.Thm_Formalism_L2_Th1_B_Jets_constantCoeff_law_pair
import Theorems.Thm_Formalism_L2_Th1_B_Jets_constantCoeff_law_three
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst


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
    (h1 : PowerSeries.coeff 1 l = 1) (j : Fin 3) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U3 F) g) = PowerSeries.subst (U3 F) (Dinv l g) := by
  rw [Dj_psubst h1 j g (constantCoeff_law_three hF)]
  have e1 : PowerSeries.subst (U3 F) l =
      PowerSeries.subst (U2 F 0 1) l +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) l := by
    unfold U3
    exact law_subst hF hc (constantCoeff_law_pair hF 0 1) (ccX 2)
  have e2 : PowerSeries.subst (U2 F 0 1) l =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) l :=
    law_subst hF hc (ccX 0) (ccX 1)
  have k0 := key h1 j 0
  have k1 := key h1 j 1
  have k2 := key h1 j 2
  simp only [pd] at k0 k1 k2
  rw [e1, e2]
  simp only [pd, map_add, mul_add]
  rw [k0, k1, k2]
  have hsum : ((if (0 : Fin 3) = j then 1 else 0) + (if (1 : Fin 3) = j then 1 else 0) +
      (if (2 : Fin 3) = j then 1 else 0) : MvPowerSeries (Fin 3) K) = 1 := by
    fin_cases j <;> simp
  rw [← mul_add, ← mul_add, hsum, mul_one]
end Formalism.L2.Th1.B.Jets
