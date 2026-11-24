-- Prove2me | solution 1 for Formalism.HC.Der.ordCompl_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:35.967969+00:00
-- url     : https://prove2.me/submissions/87fc8dc3-66e1-407d-92f3-a99099317ebb

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_cop_QSq_d
import Theorems.Thm_Formalism_HC_D7_ordCompl_eq


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
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hd : H.d.Prime := H.hyp.2.1
  have hnd : ¬ H.d ∣ H.QS * H.q := fun h => hd.one_lt.ne' ((cop_QSq_d H).symm.eq_one_of_dvd h)
  show ordCompl[H.d] (H.QS * H.q * H.d) = H.QS * H.q
  rw [show H.QS * H.q * H.d = H.d ^ 1 * (H.QS * H.q) by ring]
  exact Formalism.HC.D7.ordCompl_eq hd 1 hnd
end Formalism.HC.Der
