-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsLev.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:18.923891+00:00
-- url     : https://prove2.me/submissions/63e1444b-c965-4848-866d-ad5eea12264c

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
namespace IsLev
theorem _root_.solution {ρ : W → Module.End ℂ V} {L X Y : AddSubgroup W} {k : ℕ} {G : V} (h : IsLev ρ L X Y k G) (j : ℕ) :
    IsLev ρ L X Y (k * j) G := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [← smul_smul]
    exact h.1 _ (AddSubgroup.nsmul_mem _ hu j)
  · rw [← smul_smul]
    exact h.2 _ (AddSubgroup.nsmul_mem _ hu j)
end IsLev
end Formalism.IndefR.Fin.Four
