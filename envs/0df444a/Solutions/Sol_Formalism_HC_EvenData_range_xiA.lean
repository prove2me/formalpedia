-- Prove2me | solution 1 for Formalism.HC.EvenData.range_xiA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:34.55606+00:00
-- url     : https://prove2.me/submissions/9453677f-7561-47c2-aff8-c80f135b5aef

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Theorems.Thm_Formalism_HC_EvenData_xiA_toA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)
namespace Formalism.HC.EvenData
theorem _root_.solution : D.xiA.range = D.ξ.range := by
  have h : D.ξ = D.xiA.comp D.toA := MonoidHom.ext fun u => (D.xiA_toA u).symm
  rw [h, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr D.toA_surj, ← MonoidHom.range_eq_map]
end Formalism.HC.EvenData
