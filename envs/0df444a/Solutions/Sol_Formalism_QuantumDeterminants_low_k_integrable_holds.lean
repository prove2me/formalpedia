-- Prove2me | solution 1 for Formalism.QuantumDeterminants.low_k_integrable_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:52.274603+00:00
-- url     : https://prove2.me/submissions/4c2f3d49-3523-4876-83ca-a8cfda3b8e08

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Theorems.Thm_Formalism_QuantumDeterminants_dslowk_lowK_eq

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
theorem _root_.solution : LowKInt := by
  intro n ε lam h a
  obtain ⟨m, hm⟩ := h a
  refine ⟨m + n - 1 - a - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) +
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  rw [dslowk_lowK_eq]
  unfold rhoC
  push_cast
  linarith
end Formalism.QuantumDeterminants
