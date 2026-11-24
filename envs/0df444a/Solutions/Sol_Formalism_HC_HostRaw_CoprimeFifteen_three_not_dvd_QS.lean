-- Prove2me | solution 1 for Formalism.HC.HostRaw.CoprimeFifteen.three_not_dvd_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:03:42.220543+00:00
-- url     : https://prove2.me/submissions/fae27554-f030-4d4b-af7c-06b44f1c67f2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
variable {H}
namespace Formalism.HC.HostRaw
namespace CoprimeFifteen
theorem _root_.solution (h : H.CoprimeFifteen) : ¬ 3 ∣ H.QS :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    ((show Nat.Coprime H.QS 15 from h).coprime_dvd_right (by norm_num : 3 ∣ 15)).symm
end CoprimeFifteen
end Formalism.HC.HostRaw
