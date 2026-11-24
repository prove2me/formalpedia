-- Prove2me | solution 1 for Formalism.L2.NCov.pow_sub_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:50.926214+00:00
-- url     : https://prove2.me/submissions/01ab7e34-4950-4829-a67e-39fd36cddf6d

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_W_le
import Theorems.Thm_Formalism_L2_NCov_algebraMap_end_eq

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
open Polynomial
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution [FiniteDimensional K V] (ψ : Algebra.adjoin O S →ₐ[O] O)
    (t : Algebra.adjoin O S) {x : V} (hx : x ∈ W _ (pt ψ)) :
    (((t : End K V) - algebraMap O (End K V) (ψ t)) ^
      ((t : End K V).maxGenEigenspaceIndex (pt ψ t))) x = 0 := by
  have h1 := W_le _ (pt ψ) t hx
  rw [maxGenEigenspace_eq, mem_genEigenspace_nat] at h1
  rw [algebraMap_end_eq]
  exact h1
end Formalism.L2.NCov
