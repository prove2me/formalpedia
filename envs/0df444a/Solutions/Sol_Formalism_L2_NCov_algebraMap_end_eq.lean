-- Prove2me | solution 1 for Formalism.L2.NCov.algebraMap_end_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:41.974207+00:00
-- url     : https://prove2.me/submissions/99b81d95-c959-44b0-a98d-9ac4774074fd

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
namespace Formalism.L2.NCov
theorem _root_.solution (c : O) :
    algebraMap O (End K V) c = (algebraMap O K c) • (1 : End K V) := by
  ext x
  simp [Module.algebraMap_end_apply, algebraMap_smul]
end Formalism.L2.NCov
