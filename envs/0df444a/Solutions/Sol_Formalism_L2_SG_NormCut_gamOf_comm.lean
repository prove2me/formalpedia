-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.gamOf_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:54.235324+00:00
-- url     : https://prove2.me/submissions/f6280568-8037-4320-8ba2-9701f45d5179

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type*} [Group I] [Fintype I]
namespace Formalism.L2.SG.NormCut
theorem _root_.solution (U : Set I) (p : I → ℂ) (x y : I) : gamOf U p (x * y) = gamOf U p (y * x) := by
  unfold gamOf
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight y)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  group
end Formalism.L2.SG.NormCut
