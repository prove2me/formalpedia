-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_inl_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:31.974972+00:00
-- url     : https://prove2.me/submissions/094ba5d1-9837-4838-a165-d26afad30fdb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_derivation_ext_of_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply


section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
private theorem derivation_comp_algebraMap_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k T T) (s : S) :
    derivationCompAlgebraMap k S T D s = D (algebraMap S T s) := rfl
private theorem algebraMap_comp_derivation_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i))
      = algebraMapCompDerivation k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]
    by_cases hij : i = j
    · subst hij
      rw [partialDeriv_coord_self, partialDeriv_coord_self, map_one]
    · rw [partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij),
        partialDeriv_coord_of_ne k ι S i j hij, map_zero]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply] at h2
  exact h2
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
