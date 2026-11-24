-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartAlgebra_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:36.290794+00:00
-- url     : https://prove2.me/submissions/2eb2d032-df3f-48b0-809a-f8a005e60463

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartEvalHom_C

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
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    letI : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    IsScalarTower Γ(X, W) (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show (h.appLE W V e).hom a = chartEvalHom hW g (algebraMap Γ(X, W) (MvPolynomial n Γ(X, W)) a)
  rw [MvPolynomial.algebraMap_eq, chartEvalHom_C hW h e g hg]
end FunctorialResolution.EmbeddedResolution
