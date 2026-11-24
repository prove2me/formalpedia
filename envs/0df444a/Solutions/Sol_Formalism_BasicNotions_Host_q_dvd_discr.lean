-- Prove2me | solution 1 for Formalism.BasicNotions.Host.q_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:26.045743+00:00
-- url     : https://prove2.me/submissions/5155284c-a607-42a0-9659-8044c5875a37

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Theorems.Thm_Formalism_HC_dvd_discr_of_sqrt

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
theorem _root_.solution : (H.q : ℤ) ∣ discr H.E := Formalism.HC.dvd_discr_of_sqrt H.E H.q_prime H.sqq_sq
end Formalism.BasicNotions.Host
