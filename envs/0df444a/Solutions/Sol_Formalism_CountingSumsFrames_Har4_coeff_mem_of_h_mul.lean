-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.coeff_mem_of_h_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:15.780579+00:00
-- url     : https://prove2.me/submissions/7eaeba14-9da7-4e07-82e3-7369957ce9f2

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (R : Subring K) (i0 : Fin k) (G : PolXY K k)
    (hG : ∀ m, coeff m (hXY K k * G) ∈ R) : ∀ m, coeff m G ∈ R := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0⟩ := hcon
  set S := G.support.filter (fun m => coeff m G ∉ R) with hS
  have hne : S.Nonempty := ⟨m0, by
    rw [hS, Finset.mem_filter, MvPolynomial.mem_support_iff]
    exact ⟨fun h => hm0 (h ▸ R.zero_mem), hm0⟩⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S (fun m => m (Sum.inl i0)) hne
  have hbig : ∀ m' : XY k →₀ ℕ, m (Sum.inl i0) < m' (Sum.inl i0) → coeff m' G ∈ R := by
    intro m' hlt
    by_contra hc
    have : m' ∈ S := by
      rw [hS, Finset.mem_filter, MvPolynomial.mem_support_iff]
      exact ⟨fun h => hc (h ▸ R.zero_mem), hc⟩
    have := hmax m' this
    omega
  have hmR : coeff m G ∉ R := (Finset.mem_filter.1 hmS).2
  apply hmR
  set M : XY k →₀ ℕ := Finsupp.single (Sum.inl i0) 1 + (Finsupp.single (Sum.inr i0) 1 + m) with hM
  have h1 := hG M
  rw [hXY, Finset.sum_mul, coeff_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at h1
  have h2 : coeff M (X (Sum.inl i0) * X (Sum.inr i0) * G) = coeff m G := by
    rw [mul_assoc, hM, coeff_X_mul, coeff_X_mul]
  have h3 : ∑ i ∈ Finset.univ.erase i0, coeff M (X (Sum.inl i) * X (Sum.inr i) * G) ∈ R := by
    refine R.sum_mem fun i hi => ?_
    have hi' : i ≠ i0 := Finset.ne_of_mem_erase hi
    rw [mul_assoc, coeff_X_mul']
    split_ifs with ha
    · rw [coeff_X_mul']
      split_ifs with hb
      · apply hbig
        simp [hM, hi']
      · exact R.zero_mem
    · exact R.zero_mem
  rw [h2] at h1
  have := R.sub_mem h1 h3
  simpa using this
end Formalism.CountingSumsFrames.Har4
