-- Prove2me | solution 1 for Formalism.LatticeIndexTer.subgroupData.length_le_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:43.526392+00:00
-- url     : https://prove2.me/submissions/bbd78dbe-3895-452d-980d-de7931843026

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
namespace Formalism.LatticeIndexTer.subgroupData
theorem _root_.solution {S A B : Submodule O X} (hBA : B ≤ A) :
    Module.length O (S ⧸ A.comap S.subtype) ≤ Module.length O (S ⧸ B.comap S.subtype) := by
  let g : (S ⧸ B.comap S.subtype) →ₗ[O] (S ⧸ A.comap S.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hBA hx)
  apply Module.length_le_of_surjective g
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk z, rfl⟩
end Formalism.LatticeIndexTer.subgroupData
