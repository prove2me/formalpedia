-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_det_basisKaehler
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:11.974574+00:00
-- url     : https://prove2.me/submissions/c8180c0b-01f5-48d1-ad9d-4a53a0f5b859

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange


section
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
section
end
section
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S'] [Algebra S S']
  [IsScalarTower (MvPolynomial ι k) S S']
end
section
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
  [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
  [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
  [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']
private theorem repr_map_basisKaehler
    (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
    [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
    [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
    [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
    [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']
    (ω : KaehlerDifferential k S) (i : ι) :
    (basisKaehler k ι S').repr (KaehlerDifferential.map k k S S' ω) i
      = algebraMap S S' ((basisKaehler k ι S).repr ω i) := by
  have hb : ∀ j : ι, KaehlerDifferential.map k k S S' (basisKaehler k ι S j)
      = basisKaehler k ι S' j := by
    intro j
    simp only [basisKaehler_apply, KaehlerDifferential.map_D,
      algebraMap_coord]
  have hω : ω = ∑ j : ι, (basisKaehler k ι S).repr ω j • basisKaehler k ι S j :=
    ((basisKaehler k ι S).sum_repr ω).symm
  have key : KaehlerDifferential.map k k S S' ω
      = ∑ j : ι, algebraMap S S' ((basisKaehler k ι S).repr ω j) • basisKaehler k ι S' j := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' ((basisKaehler k ι S).repr ω j) (basisKaehler k ι S' j)
  rw [key]
  simp only [Module.Basis.repr_sum_self]
end
section
end
section
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
  [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
  [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
  [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (v : ι → S) :
    algebraMap S S' ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (v i)) =
      (basisKaehler k ι S').det
        fun i : ι => KaehlerDifferential.D k S' (algebraMap S S' (v i)) := by
  have hmat : (algebraMap S S').mapMatrix
        ((basisKaehler k ι S).toMatrix fun i : ι => KaehlerDifferential.D k S (v i))
      = (basisKaehler k ι S').toMatrix
        fun i : ι => KaehlerDifferential.D k S' (algebraMap S S' (v i)) := by
    ext i j
    have h0 : KaehlerDifferential.D k S' (algebraMap S S' (v j))
        = KaehlerDifferential.map k k S S' (KaehlerDifferential.D k S (v j)) := by
      simp only [KaehlerDifferential.map_D]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, h0]
    exact (repr_map_basisKaehler k ι S S' (KaehlerDifferential.D k S (v j)) i).symm
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det, hmat]
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
