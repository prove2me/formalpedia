-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.smulSub_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:42.267515+00:00
-- url     : https://prove2.me/submissions/589ece03-ae31-41ec-99ed-900fab9a26a8

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
theorem _root_.solution (k j : ℕ) (H : AddSubgroup W) : smulSub (k * j) H ≤ smulSub k H := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_smulSub.1 hx
  exact mem_smulSub.2 ⟨j • u, H.nsmul_mem hu j, by rw [smul_smul]⟩
end Formalism.IndefR.Fin.Four
