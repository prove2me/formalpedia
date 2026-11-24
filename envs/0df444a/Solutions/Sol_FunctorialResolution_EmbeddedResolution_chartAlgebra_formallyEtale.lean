-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartAlgebra_formallyEtale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:31.595729+00:00
-- url     : https://prove2.me/submissions/8165dfeb-1c1d-49bd-992d-ec790ca75cbe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAlgebra_etale

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
theorem _root_.solution (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g] :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.FormallyEtale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra_etale hW hV g
  infer_instance
end FunctorialResolution.EmbeddedResolution
