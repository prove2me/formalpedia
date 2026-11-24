-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.piK_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.92486+00:00
-- url     : https://prove2.me/submissions/1eaa3c27-46ab-4729-8d39-168ca8a4f162

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
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (G H : V) :
    piK ρ L X Y k (G + H) = piK ρ L X Y k G + piK ρ L X Y k H := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib]
end Formalism.IndefR.Fin.Four
