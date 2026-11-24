-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelliHighestWeight_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:31.887823+00:00
-- url     : https://prove2.me/submissions/1f6c1be0-6d8c-47f1-a8ba-d55452ed0c5f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio
import Theorems.Thm_Formalism_REAL_quantumDetHighestWeight_holds


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
theorem _root_.solution : CapelliHW := by
  intro V _ _ n E ν v hG hHW Y
  rw [quantumDetHighestWeight_holds V n E ν v hG hHW]
  congr 1
  unfold capP
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [rhoStd]
  push_cast
  ring
end Formalism.QuantumDeterminants
