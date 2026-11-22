-- Prove2me | solution 1 for Formalism.L2.NCov.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:12.903007+00:00
-- url     : https://prove2.me/submissions/d2da7bd3-2fc1-41ba-8ac3-df590463a04e

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
theorem _root_.solution {T : Subalgebra O (End K V)} (hinj : Function.Injective (algebraMap O K)) :
    Function.Injective (pt : (T →ₐ[O] O) → T → K) := fun ψ ψ' h =>
  AlgHom.ext fun t => hinj (congrFun h t)
end Formalism.L2.NCov
