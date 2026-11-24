-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelliPolynomialPermInvariant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:41.054854+00:00
-- url     : https://prove2.me/submissions/bacfa130-8c7e-42df-9bd0-dab1c3b848f8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CapPPerm := by
  intro n lam σ Y
  unfold capP
  exact Equiv.prod_comp σ (fun s => Y + lam s)
end Formalism.QuantumDeterminants
