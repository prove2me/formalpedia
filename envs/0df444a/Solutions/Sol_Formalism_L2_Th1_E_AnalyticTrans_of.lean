-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnalyticTrans_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:22:50.979815+00:00
-- url     : https://prove2.me/submissions/e40545d3-d113-4b61-9e0a-832846380d6d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_norm_natCast
import Theorems.Thm_Formalism_L2_Th1_E_Tor_nsmul_ptOf
import Theorems.Thm_Formalism_L2_Th1_E_Tor_restrict
import Theorems.Thm_Formalism_L2_Th1_E_Tor_cc_gT
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Tor
open Classical
namespace Formalism.L2.Th1.E
theorem _root_.solution (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hU : TransUnit) : AnalyticTrans := by
  intro l _ L ι hW t N hN hlN hNt ht
  obtain ⟨hIP, hTS⟩ := restrict l L ι hS hA hZ hI hW t N hN hlN hNt
  have h := hU ℂ_[l] (curveL l L ι) hW (AddSubgroup.zmultiples t) _ _ hIP hTS
    ⟨t, AddSubgroup.mem_zmultiples t⟩ N (norm_natCast l hlN)
    (by
      change N • ptOf l L ι t = 0
      rw [nsmul_ptOf l L ι hA hZ]
      exact (hZ l L ι _).2 hNt)
    (fun h0 => ht ((hZ l L ι t).1 h0))
  simpa only [cc_gT] using h
end Formalism.L2.Th1.E
