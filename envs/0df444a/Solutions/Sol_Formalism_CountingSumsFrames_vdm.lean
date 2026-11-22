-- Prove2me | solution 1 for Formalism.CountingSumsFrames.vdm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:53.687769+00:00
-- url     : https://prove2.me/submissions/cf3f39c0-23c4-49bd-bd93-35d5195c9977

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {K σ : Type} [Field K]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (H : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (f : (σ →₀ ℕ) → ℤ) [CharZero K]
    (hH : ∀ x m, coeff m (H x) = ((f m : ℤ) : K) * coeff m x) (S : Submodule K (MvPolynomial σ K))
    (hS : ∀ x ∈ S, H x ∈ S) : ∀ x ∈ S, ∀ k : ℤ, compP (fun m => f m = k) x ∈ S := by
  intro x hx k
  suffices key : ∀ t : Finset ℤ, ∀ x ∈ S, (∀ m ∈ x.support, f m ∈ t) →
      ∀ k : ℤ, compP (fun m => f m = k) x ∈ S from
    key (x.support.image f) x hx (fun m hm => Finset.mem_image_of_mem f hm) k
  intro t
  induction t using Finset.induction_on with
  | empty =>
    intro x _ hsupp k
    have hx0 : x = 0 := by
      ext m
      by_contra hne
      have := hsupp m (MvPolynomial.mem_support_iff.mpr hne)
      simp at this
    have h0 : compP (fun m => f m = k) x = 0 := by
      ext m
      rw [coeff_compP, hx0]
      simp
    rw [h0]
    exact S.zero_mem
  | @insert a t ha ih =>
    intro x hx hsupp
    have hyS : H x - ((a : ℤ) : K) • x ∈ S := S.sub_mem (hS x hx) (S.smul_mem _ hx)
    have hy : ∀ m, coeff m (H x - ((a : ℤ) : K) • x) = (((f m : ℤ) : K) - ((a : ℤ) : K)) * coeff m x := by
      intro m
      rw [coeff_sub, coeff_smul, smul_eq_mul, hH]
      ring
    have hysupp : ∀ m ∈ (H x - ((a : ℤ) : K) • x).support, f m ∈ t := by
      intro m hm
      rw [MvPolynomial.mem_support_iff, hy] at hm
      have hxm : coeff m x ≠ 0 := right_ne_zero_of_mul hm
      have hfa : f m ≠ a := by
        intro h
        apply hm
        rw [h, sub_self, zero_mul]
      have := hsupp m (MvPolynomial.mem_support_iff.mpr hxm)
      rw [Finset.mem_insert] at this
      exact this.resolve_left hfa
    have hne : ∀ k : ℤ, k ≠ a → compP (fun m => f m = k) x ∈ S := by
      intro k hk
      have hka : ((k : ℤ) : K) - ((a : ℤ) : K) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hk
      have hrel : compP (fun m => f m = k) x =
          (((k : ℤ) : K) - ((a : ℤ) : K))⁻¹ • compP (fun m => f m = k) (H x - ((a : ℤ) : K) • x) := by
        ext m
        simp only [coeff_smul, smul_eq_mul, coeff_compP, hy]
        by_cases h : f m = k
        · rw [if_pos h, if_pos h, h, inv_mul_cancel_left₀ hka]
        · rw [if_neg h, if_neg h, mul_zero]
      rw [hrel]
      exact S.smul_mem _ (ih _ hyS hysupp k)
    intro k
    by_cases hk : k = a
    · rw [hk]
      have hdec : compP (fun m => f m = a) x = x - ∑ k' ∈ t, compP (fun m => f m = k') x := by
        ext m
        simp only [coeff_sub, coeff_sum, coeff_compP]
        by_cases hc : coeff m x = 0
        · simp [hc]
        · have hm := hsupp m (MvPolynomial.mem_support_iff.mpr hc)
          rw [Finset.mem_insert] at hm
          by_cases hfk : f m = a
          · rw [if_pos hfk, Finset.sum_eq_zero, sub_zero]
            intro k' hk'
            exact if_neg (fun h => ha (by rw [← hfk, h]; exact hk'))
          · rw [if_neg hfk, Finset.sum_eq_single (f m), if_pos rfl, sub_self]
            · intro b _ hb
              rw [if_neg (Ne.symm hb)]
            · intro hn
              exact absurd (hm.resolve_left hfk) hn
      rw [hdec]
      refine S.sub_mem hx (S.sum_mem fun k' hk' => hne k' ?_)
      rintro rfl
      exact ha hk'
    · exact hne k hk
end Formalism.CountingSumsFrames
