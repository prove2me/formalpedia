-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:32:32.945699+00:00
-- url     : https://prove2.me/submissions/e4d35f74-35b3-47e6-9bdd-5ded7ced06f5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_C

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
namespace EtaleChart
theorem _root_.solution (c : EtaleChart p U m) :
    @IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
      (@Algebra.toSMul k (MvPolynomial (ULift.{u} (Fin m)) k) _ _ _)
      (@Algebra.toSMul (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra)
      (@Algebra.toSMul k Γ(X, U) _ _ (sectionsAlgebra k p U)) := by
  let instPoly : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instBase : Algebra k Γ(X, U) := sectionsAlgebra k p U
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  exact (EtaleChart.coordRingHom_C c x).symm
end EtaleChart
end FunctorialResolution.EmbeddedResolution
