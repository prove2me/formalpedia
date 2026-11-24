-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_map_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:33.97582+00:00
-- url     : https://prove2.me/submissions/f10bfc18-3c08-4377-9abd-c7b53707c163

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_derivation_ext_of_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (i : ι) (hiT : i ∉ T) (f : S) :
    partialDeriv k ι S₁ i (φ f) = φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have halg : ∀ x : S, algebraMap S S₁ x = φ x := fun x => rfl
  have : IsScalarTower k S S₁ :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [halg]; exact (φ.commutes x).symm
  have hsmul : ∀ (a : S) (x : S₁), a • x = φ a * x := by
    intro a x
    rw [Algebra.smul_def, halg]
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have h₁ : ∀ a b : S,
      ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) (a * b)
        = a • ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) b
          + b • ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) a := by
    intro a b
    show partialDeriv k ι S₁ i (φ (a * b))
        = a • partialDeriv k ι S₁ i (φ b) + b • partialDeriv k ι S₁ i (φ a)
    rw [map_mul, Derivation.leibniz]
    simp only [hsmul, smul_eq_mul]
  have h₂ : ∀ a b : S,
      ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) (a * b)
        = a • ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) b
          + b • ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) a := by
    intro a b
    show φ (partialDeriv k ι S i (a * b))
        = a • φ (partialDeriv k ι S i b) + b • φ (partialDeriv k ι S i a)
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hsmul]
  have key :
      Derivation.mk' ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) h₁
        = Derivation.mk' ((φ.toLinearMap : S →ₗ[k] S₁).comp
            (partialDeriv k ι S i).toLinearMap) h₂ := by
    refine derivation_ext_of_coord k ι S S₁ _ _ ?_
    intro j
    show partialDeriv k ι S₁ i (φ (coord k ι S j)) = φ (partialDeriv k ι S i (coord k ι S j))
    by_cases hj : j ∈ T
    · by_cases hjs : j = s
      · rw [hjs, hs, partialDeriv_coord_of_ne k ι S₁ i s his,
          partialDeriv_coord_of_ne k ι S i s his, map_zero]
      · have hij : i ≠ j := fun h => hiT (by rw [h]; exact hj)
        rw [hin j hj hjs, Derivation.leibniz, partialDeriv_coord_of_ne k ι S₁ i s his,
          partialDeriv_coord_of_ne k ι S₁ i j hij, partialDeriv_coord_of_ne k ι S i j hij,
          smul_zero, smul_zero, add_zero, map_zero]
    · rw [hout j hj, partialDeriv_coord, partialDeriv_coord]
      split_ifs with h
      · exact (map_one φ).symm
      · exact (map_zero φ).symm
  exact DFunLike.congr_fun key f
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
