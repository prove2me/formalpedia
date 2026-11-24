-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.isoW_le_isoC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:17.718683+00:00
-- url     : https://prove2.me/submissions/288385f7-ce56-42da-adf7-9312f73cb49f

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_PolLeISupIsoW
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) ≤ IsoC p LL j Cs la := by
  rw [isoC_eq]
  unfold IsoW GlW.gS
  exact sInf_le_sInf fun U hU => ⟨fun v hv => hU.1 hv.1, hU.2⟩
end Formalism.InvariantFactorPaths.PW
