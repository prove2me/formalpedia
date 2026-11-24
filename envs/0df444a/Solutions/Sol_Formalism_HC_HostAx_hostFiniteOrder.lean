-- Prove2me | solution 1 for Formalism.HC.HostAx.hostFiniteOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:00:40.114853+00:00
-- url     : https://prove2.me/submissions/b37b304e-76b3-41ea-b063-df4ae3874342

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_Orbits_dim_bound


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
theorem _root_.solution (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) H.E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ 4 * φ.ord * k := by
  have h := Orbits.dim_bound k g hg M hM hne
  rw [H.der.finrank_E] at h
  exact h
end Formalism.HC.HostAx
