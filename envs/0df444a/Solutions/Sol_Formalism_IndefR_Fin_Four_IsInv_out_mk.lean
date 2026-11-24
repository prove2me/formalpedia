-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsInv.out_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:31.148751+00:00
-- url     : https://prove2.me/submissions/0c71fdc0-ea99-44da-b621-b438dd4e8724

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_mk_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
namespace Formalism.IndefR.Fin.Four
namespace IsInv
theorem _root_.solution {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (x : H) :
    g (((QuotientAddGroup.mk x : Qt k H).out : H) : W) = g x :=
  hg.mk_eq (QuotientAddGroup.out_eq' _)
end IsInv
end Formalism.IndefR.Fin.Four
