-- Prove2me | solution 1 for Formalism.L2.Th1.A.ISer.subHom_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:03.626633+00:00
-- url     : https://prove2.me/submissions/b154a3cf-6a51-4893-ae84-27625a31d99a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ISer
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.ISer
theorem _root_.solution (s : R⟦X⟧) (hs : constantCoeff s = 0) : subHom s hs X = s := by
  rw [subHom_apply, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero' hs)]
end Formalism.L2.Th1.A.ISer
