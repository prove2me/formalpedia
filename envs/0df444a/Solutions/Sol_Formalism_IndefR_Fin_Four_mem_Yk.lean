-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.mem_Yk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:34.789907+00:00
-- url     : https://prove2.me/submissions/3357e778-8768-4aac-b963-15aa8123eb3c

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac

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
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {L Y : AddSubgroup W} {k : ℕ} {y : W} : y ∈ Yk L Y k ↔ y ∈ Y ∧ k • y ∈ L := by
  simp [Yk, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
end Formalism.IndefR.Fin.Four
