-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.integ_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:35.189617+00:00
-- url     : https://prove2.me/submissions/5243edf6-0964-4355-8fe2-13df9a6c6216

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_congr
import Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec

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
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {g : W → ℂ} (h : ∀ t ∈ H, g t = 0) : integ H g = 0 := by
  have h1 : integ H g = integ H (fun t => (0 : ℂ) * (fun _ => (1 : ℂ)) t) :=
    integ_congr hfin fun t ht => by simp [h t ht]
  rw [h1, integ_cmul' hfin, zero_mul]
end Formalism.IndefR.Fin.Four
