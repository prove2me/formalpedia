-- Prove2me | solution 1 for Formalism.L2.Host.ramificationIdx_eq_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:20:48.21318+00:00
-- url     : https://prove2.me/submissions/af78ea33-77f7-4a00-8412-e1c7070d4843

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_Formalism_L2_Host_ramificationIdx_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Ideal
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.BasicNotions Formalism.FrobeniusOrbits
variable {R : Ranks} (H : Formalism.BasicNotions.Host R)
namespace Formalism.L2.Host
theorem _root_.solution (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.ramificationIdx ℤ = 1 := by
  exact ramificationIdx_eq_one H p hnd P
end Formalism.L2.Host
