-- Prove2me | solution 1 for Formalism.L2.NCov.cls_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:08.082811+00:00
-- url     : https://prove2.me/submissions/5ba505fa-25e5-4ef4-a03b-19403877cc28

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
namespace Formalism.L2.NCov
theorem _root_.solution {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : (cls ψ).IsMaximal := by
  refine RingHom.ker_isMaximal_of_surjective _ fun y => ?_
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨algebraMap O T c, by simp⟩
end Formalism.L2.NCov
