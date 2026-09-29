-- Prove2me | solution 1 for Deformation.exists_weakly_initial_of_corepresentableBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/79a8de05-d912-55b8-96ff-81ad11fd3332

import Mathlib
import Definitions.Def_Deformations_LiftFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_weakly_initial_of_corepresentableBy

set_option autoImplicit false
open CategoryTheory

universe u

theorem solution
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    {F : Subfunctor (Deformation.repnFunctor n G 𝓞)} {R : Deformation.ProartinianCat 𝓞}
    (e : F.toFunctor.CorepresentableBy R) :
    ∃ T : F.toFunctor.Elements, ∀ X : F.toFunctor.Elements, Nonempty (T ⟶ X) :=
  ⟨Functor.Elements.initialOfCorepresentableBy e,
    fun X => ⟨(Functor.Elements.isInitialOfCorepresentableBy e).to X⟩⟩

end S_Deformation_exists_weakly_initial_of_corepresentableBy
end P2MW
export P2MW.S_Deformation_exists_weakly_initial_of_corepresentableBy (solution)
