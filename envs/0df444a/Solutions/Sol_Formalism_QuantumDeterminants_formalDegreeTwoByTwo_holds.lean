-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formalDegreeTwoByTwo_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:46.307286+00:00
-- url     : https://prove2.me/submissions/71f31b98-a13b-4bb3-a95f-f79eb69b3c93

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
theorem _root_.solution : FormalDegreeTwoByTwo := by
  intro k hk
  simp only [fdegHC, Finset.prod_filter, Fin.prod_univ_two]
  norm_num
  all_goals first | linarith | (rw [abs_of_nonneg (by linarith)]; ring)
end Formalism.QuantumDeterminants
