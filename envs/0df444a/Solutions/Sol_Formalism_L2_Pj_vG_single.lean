-- Prove2me | solution 1 for Formalism.L2.Pj.vG_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:10.372365+00:00
-- url     : https://prove2.me/submissions/2fd6c66d-d9ff-4105-a58a-1ad0143a7e8f

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
theorem _root_.solution (h0 : v 0 = ⊤) (m : M) (r : R) : vG v (AddMonoidAlgebra.single m r) = v r := by
  classical
  apply le_antisymm
  · exact (iInf_le _ m).trans (by rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same])
  · refine le_iInf fun u => ?_
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact le_rfl
    · rw [h0]; exact le_top
end Formalism.L2.Pj
