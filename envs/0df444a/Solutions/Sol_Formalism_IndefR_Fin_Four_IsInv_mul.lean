-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsInv.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:31.873336+00:00
-- url     : https://prove2.me/submissions/73f2a4a5-2278-40ad-a0da-31fde2efb146

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
namespace Formalism.IndefR.Fin.Four
namespace IsInv
theorem _root_.solution {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (j : ℕ) : IsInv (k * j) H g := by
  intro t ht u hu
  rw [← smul_smul]
  exact hg t ht _ (H.nsmul_mem hu j)
end IsInv
end Formalism.IndefR.Fin.Four
