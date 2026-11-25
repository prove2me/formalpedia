-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_isRegularParameterSystem_with_coords_of_germ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:56.139682+00:00
-- url     : https://prove2.me/submissions/aa05bb17-e57b-4bf4-9ed6-d83a89a054b8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isRegularParameterSystem_with_coords_of_mem_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) :=
  exists_isRegularParameterSystem_with_coords_of_mem_prime hU c x hx J₀
    (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj))
end FunctorialResolution.EmbeddedResolution
