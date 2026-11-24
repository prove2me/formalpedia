-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsInv.shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:27.808519+00:00
-- url     : https://prove2.me/submissions/5f9d6c0d-b443-49d9-be46-dd1c43429542

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe

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
theorem _root_.solution {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    IsInv k H (fun t => g (t + v)) := by
  intro t ht u hu
  simp only
  rw [add_right_comm, hg _ (H.add_mem ht hv) u hu]
end IsInv
end Formalism.IndefR.Fin.Four
