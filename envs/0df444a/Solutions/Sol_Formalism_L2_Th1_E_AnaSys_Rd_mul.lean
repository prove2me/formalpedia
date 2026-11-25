-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnaSys.Rd.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:29.095116+00:00
-- url     : https://prove2.me/submissions/1ecaf395-2d7c-4d98-9c56-f2494e55a2c5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_inU_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_Low_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AnaSys
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
variable {l L ι}
namespace Formalism.L2.Th1.E.AnaSys
namespace Rd
theorem _root_.solution {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l L ι f S) (hg : Rd l L ι g T) :
    Rd l L ι (fun z => f z * g z) (S * T) :=
  ⟨hf.1.mul hg.1, by rw [inU_mul l L ι hf.1 hg.1, hf.2, hg.2]⟩
end Rd
end Formalism.L2.Th1.E.AnaSys
