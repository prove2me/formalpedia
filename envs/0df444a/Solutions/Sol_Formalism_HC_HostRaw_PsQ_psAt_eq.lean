-- Prove2me | solution 1 for Formalism.HC.HostRaw.PsQ.psAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:18:13.60403+00:00
-- url     : https://prove2.me/submissions/e32c9ebe-64b6-4a43-9850-f81ad1455984

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_jacobi_neg_recip
import Theorems.Thm_Formalism_HC_jacobi_congr
import Theorems.Thm_Formalism_HC_HostRaw_q_mod_four
import Theorems.Thm_Formalism_HC_HostRaw_q_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_psAt_of_coprime
import Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
import Theorems.Thm_Formalism_HC_HostRaw_odd_of_coprime

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
namespace PsQ
theorem _root_.solution (hP : H.PsQ) {p : ℕ} (h : Nat.Coprime p H.condN) : H.psAt p = jacobiSym (-(H.q : ℤ)) p := by
  rw [H.psAt_of_coprime h, hP, jacobi_neg_recip H.q_mod_four (H.odd_of_coprime h)]
  exact jacobi_congr ((H.val_unitOfCoprime h).of_dvd H.q_dvd_condN)
end PsQ
end Formalism.HC.HostRaw
