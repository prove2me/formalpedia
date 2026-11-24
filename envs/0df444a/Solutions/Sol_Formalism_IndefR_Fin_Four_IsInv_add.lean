-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsInv.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:47.270279+00:00
-- url     : https://prove2.me/submissions/1584afa5-9a7b-4850-b539-b96b3863cdd5

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_mul

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
omit hfin
namespace Formalism.IndefR.Fin.Four
namespace IsInv
theorem _root_.solution {k k' : ℕ} {g g' : W → ℂ} (hg : IsInv k H g) (hg' : IsInv k' H g') :
    IsInv (k * k') H (fun t => g t + g' t) := by
  have h1 := hg.mul k'
  have h2 := hg'.mul k
  rw [Nat.mul_comm] at h2
  intro t ht u hu
  simp only [h1 t ht u hu, h2 t ht u hu]
end IsInv
end Formalism.IndefR.Fin.Four
