-- Prove2me | solution 1 for Formalism.L2.Pj.vG_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:52.946412+00:00
-- url     : https://prove2.me/submissions/51339e2e-371f-43c9-9aae-c9689c7e2a1d

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
variable {v : R → EReal}
namespace Formalism.L2.Pj
theorem _root_.solution (h0 : v 0 = ⊤) : vG v (0 : AddMonoidAlgebra R M) = ⊤ := by simp [vG, h0]
end Formalism.L2.Pj
