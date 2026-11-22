-- Prove2me | solution 1 for Formalism.L2.NCov.iSupIndep_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:15.006318+00:00
-- url     : https://prove2.me/submissions/f74cf028-eef0-4502-ac58-089b26e2cea2

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_commute_adjoin

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
theorem _root_.solution (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) : iSupIndep (W (Algebra.adjoin O S)) :=
  independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun t : Algebra.adjoin O S => (t : End K V))
    fun i j φ => mapsTo_maxGenEigenspace_of_comm (commute_adjoin hS j.2 i.2) φ
end Formalism.L2.NCov
