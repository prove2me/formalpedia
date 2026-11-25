-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_isRegularParameterSystem_with_coords_of_mem_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:17.698172+00:00
-- url     : https://prove2.me/submissions/d1dbd865-3b3a-4278-ace4-b25d7fc9a0c5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_sections_span_eq_maximalIdeal_with_coords

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
theorem _root_.solution (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) := by
  obtain ⟨d, f, -, h2, h3, h4⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J₀
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ₀ j hj))
  exact ⟨d, f, h2, h3, h4⟩
end FunctorialResolution.EmbeddedResolution
