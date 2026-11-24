-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsInv.mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:18.010641+00:00
-- url     : https://prove2.me/submissions/ee00c93a-0c79-41ed-bf9b-928325371368

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_smulSub

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
theorem _root_.solution {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) {x y : H}
    (hxy : (QuotientAddGroup.mk x : Qt k H) = QuotientAddGroup.mk y) : g x = g y := by
  have h := QuotientAddGroup.eq.1 hxy
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h
  have : (y : W) = x + k • u := by rw [hux]; push_cast; abel
  rw [this, hg _ x.2 u hu]
end IsInv
end Formalism.IndefR.Fin.Four
