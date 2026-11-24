-- Prove2me | solution 1 for Formalism.HC.HostAx.dvd_discr_of_dvd_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:35.069798+00:00
-- url     : https://prove2.me/submissions/9f2e0b04-21a5-4ca2-9fa6-b065c33ef78a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Theorems.Thm_Formalism_HC_dvd_discr_of_mem_sq
import Theorems.Thm_Formalism_HC_HostAx_mem_sq_of_dvd_QS


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
open Formalism Formalism.HC
namespace Formalism.HC
namespace HostAx
theorem _root_.solution {φ : Frame} (H : HostAx φ) (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) :
    (l : ℤ) ∣ discr H.E :=
  dvd_discr_of_mem_sq H.E hl fun P _ hv => H.mem_sq_of_dvd_QS hE hl hd P hv
end HostAx
end Formalism.HC
