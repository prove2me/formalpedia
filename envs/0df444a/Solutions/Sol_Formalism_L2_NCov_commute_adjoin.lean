-- Prove2me | solution 1 for Formalism.L2.NCov.commute_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:04.901567+00:00
-- url     : https://prove2.me/submissions/6d6c4b5d-dd2d-497b-b110-fe2aa4b21494

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
variable [IsLocalRing O]
variable {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {a b : End K V}
    (ha : a ∈ Algebra.adjoin O S) (hb : b ∈ Algebra.adjoin O S) : Commute a b :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b' hb' =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun a' ha' => hS b' hb' a' ha').symm
end Formalism.L2.NCov
