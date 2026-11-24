-- Prove2me | solution 1 for Formalism.L2.Th1.E.Tor.cc_gT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:22.587997+00:00
-- url     : https://prove2.me/submissions/7c877f47-f5b3-45b9-a734-753bafc4cf43

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_cc_fExp_phL
import Theorems.Thm_Formalism_L2_Th1_E_Tor_cc_inU
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul


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
open Formalism.L2.Th1.E.Tor
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
namespace Formalism.L2.Th1.E.Tor
theorem _root_.solution (t : ℂ) : constantCoeff (gT l L ι t) = ι (opU L t (sgStar L) 0) := by
  rw [gT, map_mul, cc_fExp_phL, one_mul, cc_inU]
end Formalism.L2.Th1.E.Tor
