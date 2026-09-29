-- Prove2me | solution 1 for CategoryTheory.ShortComplex.shortExact_of_mono_cokernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f4dd6e33-8b08-5646-bed1-e420c2a600e5

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem solution
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    (by change Mono f; infer_instance) (by change Epi (cokernel.π f); infer_instance)

end S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel
end P2MW
export P2MW.S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel (solution)
