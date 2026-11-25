-- Prove2me | solution 1 for Formalism.L2.Th1.E.JetIntegrality.subst_single_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:14:18.613234+00:00
-- url     : https://prove2.me/submissions/495f4263-bfca-474f-9fbb-13cd885001ad

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_JetsInOfOneVariable
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_constantCoeff_inVar_eq_zero


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp mfact)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair IsOneUnit jet)
open Formalism.L2.Th1.G (JetsIn JetsIn1)
open CompatibleChartOperations
open Formalism.L2.Th1.E.JetIntegrality
variable {K : Type} [Field K] {n : Type}
namespace Formalism.L2.Th1.E.JetIntegrality
theorem _root_.solution [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n)
    (g : PowerSeries K) :
    MvPowerSeries.subst (fun j : n => (at1 j linv : MvPowerSeries n K)) (at1 i g) =
      at1 i (PowerSeries.subst linv g) := by
  have ha : ∀ j : n, MvPowerSeries.constantCoeff (at1 j linv : MvPowerSeries n K) = 0 :=
    fun j => constantCoeff_inVar_eq_zero j h0
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold at1 at ha h ⊢
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) ha, MvPowerSeries.subst_X h,
    Formalism.L2.Th1.C.Pts.subst_subst h0 (MvPowerSeries.constantCoeff_X i)]
end Formalism.L2.Th1.E.JetIntegrality
