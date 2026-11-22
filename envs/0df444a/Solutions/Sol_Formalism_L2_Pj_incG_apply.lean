-- Prove2me | solution 1 for Formalism.L2.Pj.incG_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:25.289931+00:00
-- url     : https://prove2.me/submissions/89c70a0e-4914-476e-8f6a-6d6630f5b61b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
namespace Formalism.L2.Pj
theorem _root_.solution (w : W) (F : C w) : incG key C w F = AddMonoidAlgebra.single (key w) (F : R) := rfl
end Formalism.L2.Pj
