-- Prove2me | solution 1 for Formalism.L2.Th1.A.ISer.subHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:19.746268+00:00
-- url     : https://prove2.me/submissions/710e588c-11ce-43fc-800d-1b5495e06e37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst

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
theorem _root_.solution (s : R⟦X⟧) (hs : constantCoeff s = 0) (f : R⟦X⟧) :
    subHom s hs f = f.subst s := by
  unfold subHom
  rw [PowerSeries.coe_substAlgHom]
end Formalism.L2.Th1.A.ISer
