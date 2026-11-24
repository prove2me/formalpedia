-- Prove2me | solution 1 for Formalism.QuantumDeterminants.low_k_dominant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:07.821892+00:00
-- url     : https://prove2.me/submissions/9cd9ca59-4680-4ee1-a936-50010a55775e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Theorems.Thm_Formalism_QuantumDeterminants_low_k_differentiable_holds
import Theorems.Thm_Formalism_QuantumDeterminants_dslowk_gap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : LowKDom := by
  intro n ε lam h a b hab he
  have hd := low_k_differentiable_holds n ε lam a b hab he
  have hg := dslowk_gap h.1 h.2 hab
  rw [hd]
  linarith
end Formalism.QuantumDeterminants
