-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.avg_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:00:47.336409+00:00
-- url     : https://prove2.me/submissions/be4c0d5e-3ba3-4149-a214-2989332e91e5

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr

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
theorem _root_.solution (k : ℕ) {g g' : W → ℂ} (h : ∀ t ∈ H, g t = g' t) : avg k H g = avg k H g' := by
  rw [avg, avg]
  congr 1
  exact finsum_congr fun q => h _ (q.out : H).2
end Formalism.IndefR.Fin.Four
