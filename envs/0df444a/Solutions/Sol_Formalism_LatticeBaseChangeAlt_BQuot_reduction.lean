-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.reduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:03.435805+00:00
-- url     : https://prove2.me/submissions/4edea6b1-c180-4202-ac87-8a3f941343ad

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_mono_left
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_anti_right
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_sup_le
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_le_sup
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_triangle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
namespace Formalism.LatticeBaseChangeAlt.BQuot
theorem _root_.solution (X Θ N₀ T NK : Submodule O V) (h1 : N₀ ≤ Θ) (h2 : T ≤ Θ) :
    ql (X ⊔ Θ) Θ ≤ ql ((X ⊓ NK) ⊔ N₀) N₀ + ql X ((X ⊓ NK) ⊔ T) := by
  refine (ql_sup_le X Θ).trans ((ql_triangle X ((X ⊓ NK) ⊔ T) Θ).trans ?_)
  rw [add_comm]
  gcongr
  calc ql ((X ⊓ NK) ⊔ T) Θ ≤ ql (X ⊓ NK) Θ := ql_le_of_le_sup (sup_le_sup_left h2 _)
    _ ≤ ql (X ⊓ NK) N₀ := ql_anti_right h1
    _ ≤ ql ((X ⊓ NK) ⊔ N₀) N₀ := ql_mono_left le_sup_left
end Formalism.LatticeBaseChangeAlt.BQuot
