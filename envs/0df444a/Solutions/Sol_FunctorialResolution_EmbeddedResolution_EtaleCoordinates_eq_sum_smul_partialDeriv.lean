-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.eq_sum_smul_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:59.305579+00:00
-- url     : https://prove2.me/submissions/627da084-d99f-4a21-b1f9-cdb5a5f84477

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
include ι
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution [Fintype ι] (D : Derivation k S S) :
    D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
  ext s
  have hsum : (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) s
      = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i s :=
    sum_smul_derivation_apply k ι S (fun i => D (coord k ι S i))
      (partialDeriv k ι S) s Finset.univ
  rw [hsum]
  have h1 : D s = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by
    rw [Derivation.liftKaehlerDifferential_comp_D]
  have h2 : KaehlerDifferential.D k S s
      = ∑ i : ι, (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i
          • basisKaehler k ι S i :=
    ((basisKaehler k ι S).sum_repr (KaehlerDifferential.D k S s)).symm
  rw [h1, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul,
    ← partialDeriv_apply]
  exact mul_comm _ _
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
