-- Prove2me | solution 1 for Formalism.HC.PChar.inv_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:28.804406+00:00
-- url     : https://prove2.me/submissions/30c45d40-d305-4a18-bdf2-dc9f2716e3c7

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
attribute [instance] PChar.ne
open Formalism.HC.PChar
namespace Formalism.HC.PChar
theorem _root_.solution (ψ : PChar) : ψ.inv.inv = ψ := by
  cases ψ
  simp only [inv]
  congr 1
  exact _root_.inv_inv _
end Formalism.HC.PChar
