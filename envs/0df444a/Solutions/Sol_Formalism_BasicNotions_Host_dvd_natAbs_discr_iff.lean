-- Prove2me | solution 1 for Formalism.BasicNotions.Host.dvd_natAbs_discr_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:47:46.267314+00:00
-- url     : https://prove2.me/submissions/7f4b8e27-6a19-4689-ab3c-d990200c15bc

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Theorems.Thm_Formalism_BasicNotions_Host_dvd_discr_iff_dvd_condN

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) : p ∣ (discr H.E).natAbs ↔ p ∣ H.condN :=
  Int.natCast_dvd.symm.trans (H.dvd_discr_iff_dvd_condN hp)
end Formalism.BasicNotions.Host
