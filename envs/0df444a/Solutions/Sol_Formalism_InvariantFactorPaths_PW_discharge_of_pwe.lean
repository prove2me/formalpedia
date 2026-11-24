-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.discharge_of_pwe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:50.79255+00:00
-- url     : https://prove2.me/submissions/b11feda7-9aba-4291-b616-27a5db299663

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_kappa_le_height_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hP : DischargeP) (hW : DischargeW) (hE : DischargeE) : HeightBoundImplication := by
  intro p _ N r LL ρ a κ hdeg hpa hκ
  have hk := kappa_le_height_bound p N r LL a κ hdeg hpa hκ
  exact ⟨hP p N r LL ρ _ hk, hW p N r LL _ hk, hE p N r LL ρ _ hk⟩
end Formalism.InvariantFactorPaths.PW
