-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartEvalHom_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:22.844794+00:00
-- url     : https://prove2.me/submissions/8032a7f4-fc3f-404c-8483-8b0296769f88

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartEvalHom_comp_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) (a : Γ(X, W)) :
    chartEvalHom hW g (MvPolynomial.C a) = (h.appLE W V e).hom a :=
  RingHom.congr_fun (chartEvalHom_comp_C hW h e g hg) a
end FunctorialResolution.EmbeddedResolution
