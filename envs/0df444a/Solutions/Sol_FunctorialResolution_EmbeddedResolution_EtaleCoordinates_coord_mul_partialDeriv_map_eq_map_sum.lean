-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_mul_partialDeriv_map_eq_map_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:35.926408+00:00
-- url     : https://prove2.me/submissions/249158bc-96dc-4464-9a60-4a444f024911

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
    (hsT : s ∈ T) (f : S) :
    coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower k S S₁ :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hsmul : ∀ (a : S) (z : S₁), a • z = φ a * z := fun a z => Algebra.smul_def a z
  have hsum_add : ∀ x y : S,
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
        = (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
          + (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y) := by
    intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, mul_add]
  have hsum_smul : ∀ (c : k) (x : S),
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
        = c • (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x) := by
    intro c x
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.map_smul, mul_smul_comm]
  have hsum_leib : ∀ a b : S,
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
        = a * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
          + b * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a) := by
    intro a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  let L₁ : S →ₗ[k] S₁ :=
    { toFun := fun x => coord k ι S₁ s * partialDeriv k ι S₁ s (φ x)
      map_add' := by
        intro x y
        show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (x + y))
          = coord k ι S₁ s * partialDeriv k ι S₁ s (φ x)
            + coord k ι S₁ s * partialDeriv k ι S₁ s (φ y)
        rw [map_add, map_add, mul_add]
      map_smul' := by
        intro c x
        show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (c • x))
          = c • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ x))
        rw [map_smul, Derivation.map_smul, mul_smul_comm] }
  let L₂ : S →ₗ[k] S₁ :=
    { toFun := fun x => φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
      map_add' := by
        intro x y
        show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
          = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
            + φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y)
        rw [hsum_add, map_add]
      map_smul' := by
        intro c x
        show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
          = c • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
        rw [hsum_smul, map_smul] }
  have hleib1 : ∀ a b : S, L₁ (a * b) = a • L₁ b + b • L₁ a := by
    intro a b
    show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (a * b))
      = a • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ b))
        + b • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ a))
    rw [map_mul, Derivation.leibniz, hsmul a, hsmul b]
    simp only [smul_eq_mul]
    ring
  have hleib2 : ∀ a b : S, L₂ (a * b) = a • L₂ b + b • L₂ a := by
    intro a b
    show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
      = a • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
        + b • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a)
    rw [hsum_leib, map_add, map_mul, map_mul, hsmul a, hsmul b]
  have hD : Derivation.mk' L₁ hleib1 = Derivation.mk' L₂ hleib2 := by
    refine derivation_ext_of_coord k ι S S₁ _ _ fun j => ?_
    show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (coord k ι S j))
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j))
    have hsum : (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j))
        = if j ∈ T then coord k ι S j else 0 := by
      have hterm : ∀ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j)
          = if i = j then coord k ι S j else 0 := by
        intro i _
        rw [partialDeriv_coord]
        by_cases h : i = j
        · subst h
          simp
        · simp [h]
      rw [Finset.sum_congr rfl hterm]
      by_cases hj : j ∈ T
      · rw [Finset.sum_eq_single j]
        · simp [hj]
        · intro i _ hij
          rw [if_neg hij]
        · intro h
          exact absurd hj h
      · rw [if_neg hj]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hij : i ≠ j := by
          rintro rfl
          exact hj hi
        rw [if_neg hij]
    rw [hsum]
    by_cases hjs : j = s
    · subst hjs
      rw [hs, if_pos hsT, hs, partialDeriv_coord_self, mul_one]
    · by_cases hjT : j ∈ T
      · have h1 : partialDeriv k ι S₁ s (coord k ι S₁ s) = 1 :=
          partialDeriv_coord_self k ι S₁ s
        have h2 : partialDeriv k ι S₁ s (coord k ι S₁ j) = 0 :=
          partialDeriv_coord_of_ne k ι S₁ s j (Ne.symm hjs)
        rw [if_pos hjT, hin j hjT hjs, Derivation.leibniz, h1, h2]
        simp only [smul_eq_mul]
        ring
      · have hne : s ≠ j := by
          rintro rfl
          exact hjT hsT
        rw [if_neg hjT, map_zero, hout j hjT,
          partialDeriv_coord_of_ne k ι S₁ s j hne, mul_zero]
  exact DFunLike.congr_fun hD f
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
