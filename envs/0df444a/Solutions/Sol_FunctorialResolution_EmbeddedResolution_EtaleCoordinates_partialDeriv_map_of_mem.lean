-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_map_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:50.346521+00:00
-- url     : https://prove2.me/submissions/5f2d5bcb-7421-4097-b040-e4e52f34b431

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
    (i : ι) (hiT : i ∈ T) (his : i ≠ s) (f : S) :
    partialDeriv k ι S₁ i (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower k S S₁ := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap k S₁ x = φ (algebraMap k S x)
    exact (φ.commutes x).symm
  have hsmul : ∀ (a : S) (z : S₁), a • z = φ a * z := fun _ _ => rfl
  let L₁ : S →ₗ[k] S₁ := (partialDeriv k ι S₁ i).toLinearMap.comp φ.toLinearMap
  let L₂ : S →ₗ[k] S₁ :=
    (LinearMap.mulLeft k (coord k ι S₁ s)).comp
      (φ.toLinearMap.comp (partialDeriv k ι S i).toLinearMap)
  have h₁ : ∀ a b : S, L₁ (a * b) = a • L₁ b + b • L₁ a := by
    intro a b
    show partialDeriv k ι S₁ i (φ (a * b))
        = a • partialDeriv k ι S₁ i (φ b) + b • partialDeriv k ι S₁ i (φ a)
    simp only [hsmul, map_mul, (partialDeriv k ι S₁ i).leibniz, smul_eq_mul]
  have h₂ : ∀ a b : S, L₂ (a * b) = a • L₂ b + b • L₂ a := by
    intro a b
    show coord k ι S₁ s * φ (partialDeriv k ι S i (a * b))
        = a • (coord k ι S₁ s * φ (partialDeriv k ι S i b))
          + b • (coord k ι S₁ s * φ (partialDeriv k ι S i a))
    simp only [hsmul, (partialDeriv k ι S i).leibniz, smul_eq_mul, map_add, map_mul]
    ring
  have hD : Derivation.mk' L₁ h₁ = Derivation.mk' L₂ h₂ := by
    refine derivation_ext_of_coord k ι S S₁ _ _ ?_
    intro j
    show partialDeriv k ι S₁ i (φ (coord k ι S j))
        = coord k ι S₁ s * φ (partialDeriv k ι S i (coord k ι S j))
    by_cases hjT : j ∈ T
    · by_cases hjs : j = s
      · subst hjs
        rw [hs]
        simp only [partialDeriv_coord, if_neg his, map_zero, mul_zero]
      · rw [hin j hjT hjs, (partialDeriv k ι S₁ i).leibniz]
        simp only [smul_eq_mul, partialDeriv_coord, if_neg his, mul_zero, zero_add]
        by_cases hij : i = j
        · simp [hij]
        · simp [hij]
    · rw [hout j hjT]
      have hij : i ≠ j := by rintro rfl; exact hjT hiT
      simp only [partialDeriv_coord, if_neg hij, map_zero, mul_zero]
  exact DFunLike.congr_fun hD f
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
