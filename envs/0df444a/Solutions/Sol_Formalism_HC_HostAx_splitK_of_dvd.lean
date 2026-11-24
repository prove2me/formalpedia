-- Prove2me | solution 1 for Formalism.HC.HostAx.splitK_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:17.219034+00:00
-- url     : https://prove2.me/submissions/f30ea583-681e-4c30-97a6-7a6462ad7426

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostRaw_dvd_QSq_iff

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
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution {l : ℕ} (hl : l.Prime) (h : l ∣ H.QS * H.q) :
    (primesOver (span {(l : ℤ)}) (𝓞 H.K)).ncard = 2 := by
  rw [H.der.splitK l hl]
  by_cases h2 : l = 2
  · exact Or.inl h2
  right
  refine ⟨h2, ?_⟩
  rcases (H.dvd_QSq_iff hl).1 h with h' | h'
  · exact H.QS_split l hl h2 h'
  · subst h'
    exact H.hyp.2.2.2.2
end Formalism.HC.HostAx
