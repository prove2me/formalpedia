-- Prove2me | solution 1 for Formalism.BasicNotions.Host.not_dvd_discr_of_not_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:08.87945+00:00
-- url     : https://prove2.me/submissions/9b363c59-1497-465b-a091-5c85e17a3a39

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_HalfNorm
import Theorems.Thm_Formalism_BasicNotions_Host_dvd_discr_iff_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_dvd_condN_iff_small


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal
open scoped Pointwise
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h2 : p ∉ H.small) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    ¬ (p : ℤ) ∣ discr H.E := fun h => by
  rcases (H.toHostRaw.dvd_condN_iff_small hp).1 ((H.dvd_discr_iff_dvd_condN hp).1 h) with h | h | h
  exacts [h2 h, hq h, hd h]
end Formalism.BasicNotions.Host
