-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_logDerivIdeal_le_span_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:48:06.106348+00:00
-- url     : https://prove2.me/submissions/b1e2e793-3d28-4716-8cbb-b8170746aa7b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_eq_sum_smul_partialDeriv
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_eq_pow_mul_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_eq_pow_mul_of_notMem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_self_eq_pow_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_tangentDerivations_span_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_smul_mem_tangentDerivations
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
private theorem finset_sum_derivation_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {μ : Type*} (u : Finset μ) (D : μ → Derivation R A A) (x : A) :
    (∑ j ∈ u, D j) x = ∑ j ∈ u, (D j) x := by
  classical
  refine Finset.induction_on u ?_ ?_
  · simp
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    simp
private theorem smul_derivation_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (a : A) (D : Derivation R A A) (x : A) : (a • D) x = a * D x := by
  simp
variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)
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
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ) (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (logDerivIdeal k (Ideal.span {coord k ι S i}) J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)}
          * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hJmem : ∀ f ∈ J, ∃ f₁ ∈ J₁, φ f = coord k ι S₁ s ^ (e + 1) * f₁ := by
    intro f hf
    obtain ⟨f₁, hf₁, hfe⟩ := Ideal.mem_span_singleton_mul.mp (hJ (Ideal.mem_map_of_mem φ hf))
    exact ⟨f₁, hf₁, hfe.symm⟩
  have htan : ∀ j : ι, j ≠ i →
      partialDeriv k ι S₁ j ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) := by
    intro j hj
    rw [mem_tangentDerivations_span_singleton]
    rw [partialDeriv_coord_of_ne k ι S₁ j i hj]
    exact Submodule.zero_mem _
  have htanmul : (coord k ι S₁ i) • partialDeriv k ι S₁ i
      ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) :=
    smul_mem_tangentDerivations k (Ideal.span {coord k ι S₁ i})
      (Ideal.subset_span (Set.mem_singleton _)) (partialDeriv k ι S₁ i)
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    refine Ideal.mem_span_singleton_mul.mpr ⟨coord k ι S₁ s * f₁, ?_, ?_⟩
    · exact le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ (J₁.mul_mem_left _ hf₁)
    · rw [hfe]; ring
  · intro D hD f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    have hpd : ∀ j : ι, j ≠ i →
        partialDeriv k ι S₁ j f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      intro j hj
      exact derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        (partialDeriv k ι S₁ j) (htan j hj) hf₁
    have hpdi : coord k ι S₁ i * partialDeriv k ι S₁ i f₁
        ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      have h := derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        ((coord k ι S₁ i) • partialDeriv k ι S₁ i) htanmul hf₁
      rwa [smul_derivation_apply] at h
    have hDi : D (coord k ι S i) ∈ Ideal.span {coord k ι S i} :=
      (mem_tangentDerivations_span_singleton k (coord k ι S i) D).mp hD
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hDi
    have hDf : φ (D f) = ∑ j : ι, φ (D (coord k ι S j)) * φ (partialDeriv k ι S j f) := by
      have h0 : D f = ∑ j : ι, D (coord k ι S j) * partialDeriv k ι S j f := by
        conv_lhs => rw [eq_sum_smul_partialDeriv k ι S D]
        rw [finset_sum_derivation_apply]
        exact Finset.sum_congr rfl (fun j _ => smul_derivation_apply _ _ _)
      rw [h0, map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_mul φ _ _)
    rw [hDf]
    refine Ideal.sum_mem _ ?_
    intro j _
    by_cases hji : j = i
    · rw [hji]
      have h1 : φ (partialDeriv k ι S i f)
          = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i f₁ :=
        map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f f₁ e hfe
      have h2 : φ (D (coord k ι S i)) = φ a * (coord k ι S₁ i * coord k ι S₁ s) := by
        rw [← ha, map_mul, hin i hiT his]
      rw [h1, h2]
      exact Ideal.mem_span_singleton_mul.mpr
        ⟨φ a * coord k ι S₁ s * (coord k ι S₁ i * partialDeriv k ι S₁ i f₁),
          Ideal.mul_mem_left _ _ hpdi, by ring⟩
    · have hkey : φ (partialDeriv k ι S j f)
          ∈ Ideal.span {coord k ι S₁ s ^ e}
              * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
        by_cases hjT : j ∈ T
        · by_cases hjs : j = s
          · rw [hjs]
            have h1 := map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd f f₁ e hfe
            have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s f₁ + ((e + 1 : ℕ) : S₁) * f₁
                - ∑ l ∈ T.erase s, coord k ι S₁ l * partialDeriv k ι S₁ l f₁
                ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
              refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
              · exact Ideal.mul_mem_left _ _ (hpd s his.symm)
              · exact Ideal.mul_mem_left _ _
                  (le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ hf₁)
              · refine Ideal.sum_mem _ ?_
                intro l _
                by_cases hli : l = i
                · rw [hli]; exact hpdi
                · exact Ideal.mul_mem_left _ _ (hpd l hli)
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hbr, rfl⟩
          · have h1 :=
              map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd j hjT hjs f f₁ e hfe
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hpd j hji, rfl⟩
        · have h1 :=
            map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT j hjT f f₁ e hfe
          rw [h1]
          exact Ideal.mem_span_singleton_mul.mpr
            ⟨coord k ι S₁ s * partialDeriv k ι S₁ j f₁,
              Ideal.mul_mem_left _ _ (hpd j hji), by ring⟩
      exact Ideal.mul_mem_left _ _ hkey
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
