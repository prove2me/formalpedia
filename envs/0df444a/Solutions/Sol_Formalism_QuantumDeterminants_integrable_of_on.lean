-- Prove2me | solution 1 for Formalism.QuantumDeterminants.integrable_of_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:39.782814+00:00
-- url     : https://prove2.me/submissions/280d372f-e6ca-4156-a88d-9b212520e6ae

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution {φ h : (Fin m → ℂ) → ℂ} (hc : ContinuousOn φ (OmX m))
    (hs : tsupport φ ⊆ tsupport h) (hK : HasCompactSupport h) (hΩ : tsupport h ⊆ OmX m) :
    Integrable φ := by
  have hc' : Continuous φ := hc.continuous_of_tsupport_subset (isOpen_OmX m) (hs.trans hΩ)
  have hK' : HasCompactSupport φ := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hs
  exact hc'.integrable_of_hasCompactSupport hK'
end Formalism.QuantumDeterminants
