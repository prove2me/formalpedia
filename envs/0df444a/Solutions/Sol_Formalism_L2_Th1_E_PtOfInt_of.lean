-- Prove2me | solution 1 for Formalism.L2.Th1.E.PtOfInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:56.535837+00:00
-- url     : https://prove2.me/submissions/69d6d071-d6d2-46e8-b250-4c3595dbd842

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_norm_natCast
import Theorems.Thm_Formalism_L2_Th1_E_Tor_nsmul_ptOf

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
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Tor
open Classical
namespace Formalism.L2.Th1.E
theorem _root_.solution (hA : PtOfAdd) (hZ : PtOfZero) (hT : TorsionIntegral) : PtOfInt := by
  intro l _ L ι hW t N _ hlN hNt ht
  refine hT ℂ_[l] (curveL l L ι) hW (ptOf l L ι t) N (norm_natCast l hlN) ?_ ?_
  · rw [nsmul_ptOf l L ι hA hZ]
    exact (hZ l L ι _).2 hNt
  · exact fun h => ht ((hZ l L ι t).1 h)
end Formalism.L2.Th1.E
