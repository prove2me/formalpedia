-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.etaleChart_numCoords_add_one_of_hypersurface
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:38.205359+00:00
-- url     : https://prove2.me/submissions/71a8565b-1a02-428d-a1f8-832e4a388f24

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChart_numCoords_eq

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
variable {P : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : P ⟶ Spec (CommRingCat.of k))
    (H : P.IdealSheafData)
    [AlgebraicGeometry.LocallyOfFiniteType (H.subschemeι ≫ p)]
    {U : P.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j₁ : Fin n)
    (hH : restrictIdeal H U = c.coordIdeal {j₁})
    {V : H.subscheme.Opens} (_hV : IsAffineOpen V) {m' : ℕ}
    (c' : EtaleChart (H.subschemeι ≫ p) V m')
    (y : H.subscheme) (hyU : y ∈ H.subschemeι ⁻¹ᵁ U) (hyV : y ∈ V) :
    m' + 1 = n := by
  have hymem : y ∈ (H.subschemeι ⁻¹ᵁ U) ⊓ V := ⟨hyU, hyV⟩
  obtain ⟨W, hWmem, hyW, hWle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp H.subscheme.isBasis_affineOpens hymem
  have hW : IsAffineOpen W := hWmem
  have hle1 : W ≤ H.subschemeι ⁻¹ᵁ U := le_trans hWle inf_le_left
  have hle2 : W ≤ V := le_trans hWle inf_le_right
  have key := etaleChart_numCoords_eq (H.subschemeι ≫ p) hW y hyW
    ((c.restrictToSubscheme hU H {j₁} hH).restrict hle1) (c'.restrict hle2)
  have hcard : ({j₁} : Finset (Fin n)).card = 1 := Finset.card_singleton j₁
  have hlt : (j₁ : ℕ) < n := j₁.isLt
  omega
end FunctorialResolution.EmbeddedResolution
