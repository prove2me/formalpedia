-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.comap_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:38.630316+00:00
-- url     : https://prove2.me/submissions/5d1cbe7e-1f7e-486e-8ab1-1082f8e2853c

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution (I : Ideal R) (M : Submodule R X) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by
  have h := Submodule.map_smul'' I (⊤ : Submodule R M) M.subtype
  rw [Submodule.map_subtype_top] at h
  rw [← h, Submodule.comap_map_eq_of_injective M.injective_subtype]
end Formalism.G0.ManyOrbitsP
