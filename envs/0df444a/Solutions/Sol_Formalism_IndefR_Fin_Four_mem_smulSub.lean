-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.mem_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:43.397309+00:00
-- url     : https://prove2.me/submissions/d8280869-97b6-470a-b351-bfa2a1ab7e39

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
theorem _root_.solution {k : ℕ} {H : AddSubgroup W} {x : W} : x ∈ smulSub k H ↔ ∃ u ∈ H, k • u = x := by
  simp [smulSub, AddSubgroup.mem_map]
end Formalism.IndefR.Fin.Four
