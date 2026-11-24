-- Prove2me | solution 1 for Formalism.BasicNotions.Host.dvd_discr_iff_dvd_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:31:12.097373+00:00
-- url     : https://prove2.me/submissions/bcbba150-b1f6-4408-bc09-d5dcf456bca7

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Theorems.Thm_Formalism_HC_HostAx_dvd_discr_of_dvd_QS
import Theorems.Thm_Formalism_BasicNotions_Host_q_dvd_discr
import Theorems.Thm_Formalism_HC_HostRaw_dvd_condN_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ discr H.E ↔ p ∣ H.condN := by
  refine ⟨H.der.discr_primes.1 p hp, fun h => ?_⟩
  rcases (H.dvd_condN_iff hp).1 h with h | rfl | rfl
  · exact H.toHostAx.dvd_discr_of_dvd_QS H.QS_exact hp h
  · exact H.q_dvd_discr
  · exact H.der.discr_primes.2.2
end Formalism.BasicNotions.Host
