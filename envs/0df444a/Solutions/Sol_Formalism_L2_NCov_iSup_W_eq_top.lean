-- Prove2me | solution 1 for Formalism.L2.NCov.iSup_W_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:13.680193+00:00
-- url     : https://prove2.me/submissions/eef7a5e4-9614-48eb-880f-dfbde5649001

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_commute_adjoin
import Theorems.Thm_Formalism_L2_NCov_iSup_maxGen_eq_top

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
theorem _root_.solution [FiniteDimensional K V] (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) : ⨆ χ, W (Algebra.adjoin O S) χ = ⊤ :=
  iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun t : Algebra.adjoin O S => (t : End K V)) (fun a b _ => commute_adjoin hS a.2 b.2)
    (iSup_maxGen_eq_top hS hsplit)
end Formalism.L2.NCov
