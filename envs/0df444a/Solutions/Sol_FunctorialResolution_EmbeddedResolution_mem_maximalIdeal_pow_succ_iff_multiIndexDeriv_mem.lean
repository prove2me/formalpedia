-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:15.287931+00:00
-- url     : https://prove2.me/submissions/c1926015-07e4-49c9-858f-20a08da58ba1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_multiIndicesOfDegree
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_pow_succ_of_deriv_mem_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_add_unitMultiIndex_apply_first
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_mem_pow_sub
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_unitMultiIndex
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sum_unitMultiIndex
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply


section
namespace FunctorialResolution.EmbeddedResolution
open IsLocalRing
private theorem mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (r : ℕ) :
    ∀ f : R, f ∈ IsLocalRing.maximalIdeal R ^ r →
      (∀ β : Fin h → ℕ, (∑ i, β i = r) → multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R) →
      f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
  induction r with
  | zero =>
    intro f _ hβ
    have h0 := hβ (fun _ => 0) (by simp)
    rw [multiIndexDeriv_fun_zero] at h0
    simpa using h0
  | succ r ih =>
    intro f hf hβ
    have key : ∀ i, D i f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
      intro i
      refine ih (D i f) ?_ ?_
      · have h1 := multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hf
          (unitMultiIndex i)
        rw [multiIndexDeriv_unitMultiIndex, sum_unitMultiIndex] at h1
        simpa using h1
      · intro β hβ'
        have hsum : ∑ j, (β + unitMultiIndex i) j = r + 1 := by
          simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib, hβ', sum_unitMultiIndex]
        have h2 := hβ (β + unitMultiIndex i) hsum
        rwa [multiIndexDeriv_add_unitMultiIndex_apply_first D hDD β i f] at h2
    have hfx : f ∈ Ideal.span (Set.range x) ^ (r + 1) := by rw [hx]; exact hf
    have hdx : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
      intro i; rw [hx]; exact key i
    have hres := mem_pow_succ_of_deriv_mem_pow k x D hD (hunit (r + 1) (by omega)) hfx hdx
    rw [hx] at hres
    exact hres
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    (r : ℕ) {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r) :
    f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) ↔
      ∀ β ∈ multiIndicesOfDegree h r, multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro hfs β hβ
    have hβ' : ∑ i, β i = r := (mem_multiIndicesOfDegree β).mp hβ
    have hm := multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hfs β
    rw [hβ'] at hm
    have hr1 : r + 1 - r = 1 := by omega
    rw [hr1, pow_one] at hm
    exact hm
  · intro hall
    exact mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem x D hx hD hDD hunit r f hf
      (fun β hb => hall β ((mem_multiIndicesOfDegree β).mpr hb))
end FunctorialResolution.EmbeddedResolution
