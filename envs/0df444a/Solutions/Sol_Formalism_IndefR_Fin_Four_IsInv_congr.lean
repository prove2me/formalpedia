-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsInv.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:42.893804+00:00
-- url     : https://prove2.me/submissions/a3488a40-17fe-40cd-8919-9eb1e54bd815

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
theorem _root_.solution {k : ℕ} {g g' : W → ℂ} (hg : IsInv k H g) (h : ∀ t ∈ H, g t = g' t) : IsInv k H g' := by
  intro t ht u hu
  rw [← h _ ht, ← h _ (H.add_mem ht (H.nsmul_mem hu k)), hg t ht u hu]
end IsInv
end Formalism.IndefR.Fin.Four
