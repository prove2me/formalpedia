-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:55.129638+00:00
-- url     : https://prove2.me/submissions/8070d4cc-9963-46c3-b300-1681f98d0374

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_two_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_card_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution [DecidableEq K] (hq : Fintype.card K = q ^ 2) (c : K) (hc : c ^ q = c) (hc0 : c ≠ 0) :
    (univ.filter (fun x : K => x ^ (q + 1) = c)).card = q + 1 := by
  have h2 := c_two_le K q hq
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  set G := univ.filter (fun c : K => c ^ (k + 1) = 1) with hG
  have hGc : G.card ≤ k + 1 := c_card_pow_le K (k + 1) (by omega) 1
  set s := univ.filter (fun x : K => x ≠ 0) with hs
  have hsc : s.card = (k + 2) ^ 2 - 1 := by
    rw [hs, Finset.filter_ne', Finset.card_erase_of_mem (mem_univ _), card_univ, hq]
  have hmaps : ∀ x ∈ s, x ^ (k + 2 + 1) ∈ G := by
    intro x hx
    simp only [hs, hG, mem_filter, mem_univ, true_and] at hx ⊢
    rw [← pow_mul]
    have h3 : (k + 2 + 1) * (k + 1) = Fintype.card K - 1 := by
      rw [hq]
      have : (k + 2) ^ 2 = (k + 2 + 1) * (k + 1) + 1 := by ring
      omega
    rw [h3]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hle : ∀ b ∈ G, (s.filter (fun x => x ^ (k + 2 + 1) = b)).card ≤ k + 2 + 1 := fun b _ =>
    le_trans (card_le_card (by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.2)) (c_card_pow_le K (k + 2 + 1) (by omega) b)
  have hcG : c ∈ G := by
    simp only [hG, mem_filter, mem_univ, true_and]
    have : c * c ^ (k + 1) = c * 1 := by rw [mul_one, ← pow_succ']; exact hc
    exact mul_left_cancel₀ hc0 this
  have heq : s.filter (fun x => x ^ (k + 2 + 1) = c) = univ.filter (fun x => x ^ (k + 2 + 1) = c) := by
    ext x
    simp only [hs, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hx h0
    subst h0
    simp at hx
    exact hc0 hx.symm
  rw [← heq]
  by_contra hne
  have hlt : (s.filter (fun x => x ^ (k + 2 + 1) = c)).card < k + 2 + 1 := lt_of_le_of_ne (hle c hcG) hne
  have h4 : ∑ b ∈ G, (s.filter (fun x => x ^ (k + 2 + 1) = b)).card < ∑ b ∈ G, (k + 2 + 1) :=
    Finset.sum_lt_sum hle ⟨c, hcG, hlt⟩
  rw [← hsum, hsc, sum_const, smul_eq_mul] at h4
  have h5 : G.card * (k + 2 + 1) ≤ (k + 1) * (k + 2 + 1) := Nat.mul_le_mul_right _ hGc
  have h6 : (k + 2) ^ 2 = (k + 1) * (k + 2 + 1) + 1 := by ring
  omega
end Formalism.FourierDecayAlt.P.S3x6
