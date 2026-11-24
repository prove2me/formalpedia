-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.integral_pd_of_simeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:41.623468+00:00
-- url     : https://prove2.me/submissions/bfb6a78c-1f83-4f9d-b363-ef176fdd04b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_pd
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_pd_fExp
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023


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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution {ι : Type} [Finite ι] {T : MvPowerSeries ι K} (hT : Simeq T 0)
    (j : ι) : Integral (pd j T) := by
  obtain ⟨hc0, hE⟩ := hT
  rw [sub_zero] at hc0 hE
  have hneg : MvPowerSeries.constantCoeff (-T) = 0 := by rw [map_neg, hc0, neg_zero]
  have hprod : mvExp (-T) * mvExp T = 1 := by
    have e := fExp_add hneg hc0
    rw [neg_add_cancel] at e
    change fExp (-T) * fExp T = 1
    rw [← e]
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero'
  have hinvI : Integral (mvExp (-T)) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hE (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_mvExp' hc0) hprod
  have hpdT : pd j T = mvExp (-T) * pd j (mvExp T) := by
    have hpd := pd_fExp j hc0
    change pd j T = fExp (-T) * pd j (fExp T)
    rw [hpd, ← mul_assoc]
    change pd j T = mvExp (-T) * mvExp T * pd j T
    rw [hprod, one_mul]
  rw [hpdT]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hinvI (integral_pd j hE)
end Formalism.L2.Th1.B.Jets
