-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_derivIdeal_le_span_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:31:27.29395+00:00
-- url     : https://prove2.me/submissions/e8b25b4e-8c2b-44e9-a142-161f33afaf29

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_eq_pow_mul_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_eq_pow_mul_of_notMem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_self_eq_pow_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_eq_sum_smul_partialDeriv
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
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
variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)
private theorem mul_mem_span_singleton_mul {R : Type*} [CommRing R] (a : R) (I : Ideal R)
    {g : R} (hg : g ∈ I) : a * g ∈ Ideal.span ({a} : Set R) * I :=
  Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)) hg
private theorem finset_sum_smul_derivation_apply {k : Type*} [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] {ι : Type*} (t : Finset ι) (c : ι → S) (D : ι → Derivation k S S) (x : S) :
    (∑ i ∈ t, c i • D i) x = ∑ i ∈ t, c i * D i x := by
  refine Finset.cons_induction_on t ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.sum_cons, Finset.sum_cons]
    simp [ih]
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

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
theorem _root_.solution [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ) (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (derivIdeal k J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)} * derivIdeal k J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmem : ∀ x ∈ J, ∃ g ∈ J₁, φ x = coord k ι S₁ s ^ (e + 1) * g := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := Ideal.mem_span_singleton_mul.1 (hJ (Ideal.mem_map_of_mem φ hx))
    exact ⟨g, hg, hgx.symm⟩
  have hkey : ∀ x ∈ J, ∀ i : ι,
      φ (partialDeriv k ι S i x) ∈ Ideal.span {coord k ι S₁ s ^ e} * derivIdeal k J₁ := by
    intro x hx i
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    by_cases hiT : i ∈ T
    · by_cases his : i = s
      · have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ j ∈ T.erase s, coord k ι S₁ j * partialDeriv k ι S₁ j g
              ∈ derivIdeal k J₁ := by
          refine sub_mem (add_mem ?_ ?_) ?_
          · exact Ideal.mul_mem_left _ _
              (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ s) hg)
          · exact Ideal.mul_mem_left _ _ (le_derivIdeal k J₁ hg)
          · refine sum_mem fun j _ => ?_
            exact Ideal.mul_mem_left _ _
              (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ j) hg)
        rw [his, map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd x g e hgx]
        exact mul_mem_span_singleton_mul _ _ hbr
      · rw [map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his x g e hgx]
        exact mul_mem_span_singleton_mul _ _
          (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ i) hg)
    · rw [map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT i hiT x g e hgx,
        pow_succ, mul_assoc]
      exact mul_mem_span_singleton_mul _ _
        (Ideal.mul_mem_left _ _
          (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ i) hg))
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    refine Ideal.mem_comap.mpr ?_
    rw [hgx, pow_succ, mul_assoc]
    exact mul_mem_span_singleton_mul _ _
      (Ideal.mul_mem_left _ _ (le_derivIdeal k J₁ hg))
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h1 : D x = (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) x :=
      congrArg (fun E : Derivation k S S => E x) (eq_sum_smul_partialDeriv k ι S D)
    have hDx : D x = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i x := by
      rw [h1]
      exact finset_sum_smul_derivation_apply Finset.univ (fun i => D (coord k ι S i))
        (fun i => partialDeriv k ι S i) x
    rw [hDx, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hkey x hx i)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
