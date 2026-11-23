-- Prove2me | solution 1 for Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:04.659523+00:00
-- url     : https://prove2.me/submissions/b8ab1d2f-3857-4516-b802-aa5761d477c7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
open Formalism.L2.Th1.C (IntMv IntPS IsPt)
open Formalism.L2.Th1.E.CompatibleChartOperations
variable {K : Type} [Field K] {σ : Type} {R : Subring K}
namespace Formalism.L2.Th1.E.CompatibleChartOperations
theorem _root_.solution {τ : Type} [Fintype σ] (ph : PowerSeries K) {φ : σ → MvPowerSeries τ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    MvPowerSeries.subst φ (phSum ph) = ∑ i, PowerSeries.subst (φ i) ph := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  unfold phSum
  rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.coe_substAlgHom h]
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hφ, MvPowerSeries.subst_X h]
end Formalism.L2.Th1.E.CompatibleChartOperations
