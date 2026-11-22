-- Prove2me | solution 1 for Formalism.L2.NCov.W_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:04.051241+00:00
-- url     : https://prove2.me/submissions/8f4790bf-7572-4fe3-ab30-b02ca911b8f0

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
theorem _root_.solution (T : Subalgebra O (End K V)) (χ : T → K) (t : T) :
    W T χ ≤ (t : End K V).maxGenEigenspace (χ t) :=
  iInf_le (fun t : T => (t : End K V).maxGenEigenspace (χ t)) t
end Formalism.L2.NCov
