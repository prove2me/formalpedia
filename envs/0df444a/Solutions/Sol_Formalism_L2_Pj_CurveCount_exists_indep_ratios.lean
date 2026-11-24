-- Prove2me | solution 1 for Formalism.L2.Pj.CurveCount.exists_indep_ratios
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:45.674805+00:00
-- url     : https://prove2.me/submissions/f9c85172-c859-4775-a766-b7caee4f07a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CurveCountA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CurveCount
open MvPolynomial
namespace Formalism.L2.Pj.CurveCount
theorem _root_.solution {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {N D : ℕ} (x : Fin N → κ) (a : Fin N)
    (hxa : x a ≠ 0) (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1) :
    ∃ s : Finset κ, s.card = D ∧ (↑s : Set κ) ⊆ Set.range (fun i => x i / x a) ∧
      AlgebraicIndepOn K id (↑s : Set κ) := by
  classical
  have : FaithfulSMul K κ := (faithfulSMul_iff_algebraMap_injective K κ).mpr (algebraMap K κ).injective
  set r : Fin N → κ := fun i => x i / x a with hr
  let t2 : Fin (D + 1) × ↥(Finset.univ.erase a) → κ := fun p => t (p.1, p.2.1)
  set T2 : Set κ := insert (x a)⁻¹ (Set.range t2) with hT2
  set S : Set κ := Set.range r ∪ T2 with hS
  have hc : ∀ i : Fin (D + 1), ∑ k, t (i, k) * x k = if i = 0 then 1 else 0 := by
    intro i
    cases i using Fin.cases with
    | zero => simpa using hlin0
    | succ i => simpa [Fin.succ_ne_zero] using hlin i
  have hrS : ∀ k, r k ∈ Algebra.adjoin K S := fun k => Algebra.subset_adjoin (Or.inl ⟨k, rfl⟩)
  have hzS : (x a)⁻¹ ∈ Algebra.adjoin K S := Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))
  have htS : ∀ i k, k ≠ a → t (i, k) ∈ Algebra.adjoin K S := fun i k hk =>
    Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _
      ⟨(i, ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩), rfl⟩))
  have hmem : ∀ p, t p ∈ Algebra.adjoin K S := by
    rintro ⟨i, k⟩
    by_cases hk : k = a
    · rw [hk]
      have e : t (i, a) = (if i = 0 then 1 else 0) * (x a)⁻¹ - ∑ l ∈ Finset.univ.erase a, t (i, l) * r l := by
        have h := hc i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
        rw [← h, add_mul, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
        simp only [hr, div_eq_mul_inv, mul_assoc, sub_self, Finset.sum_const_zero, add_zero,
          mul_inv_cancel₀ hxa, mul_one]
      rw [e]
      refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ?_ hzS)
        (Subalgebra.sum_mem _ fun l hl => Subalgebra.mul_mem _ (htS i l (Finset.ne_of_mem_erase hl)) (hrS l))
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · exact htS i k hk
  let M := AlgebraicIndependent.matroid K κ
  have hI : M.Indep (Set.range t) := AlgebraicIndependent.matroid_indep_iff.mpr ht.to_subtype_range
  have hIS : Set.range t ⊆ M.closure S := by
    rintro _ ⟨p, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact isAlgebraic_algebraMap (⟨t p, hmem p⟩ : Algebra.adjoin K S)
  have h1 := hI.encard_le_eRk_of_subset hIS
  rw [M.eRk_closure_eq] at h1
  have h2 := M.eRk_union_le_eRk_add_eRk (Set.range r) T2
  have h3 : M.eRk T2 ≤ ((D + 1) * (N - 1) + 1 : ℕ) := by
    refine (M.eRk_le_encard T2).trans ((Set.encard_insert_le _ _).trans ?_)
    have h4 : (Set.range t2).encard ≤ ((D + 1) * (N - 1) : ℕ) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add h4 le_rfl
  have h5 : (((D + 1) * N : ℕ) : ℕ∞) ≤ (Set.range t).encard := by
    have := ht.injective.encard_range
    rwa [ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
  have hfin : M.eRk (Set.range r) ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.finite_range r).encard_lt_top.ne (M.eRk_le_encard _)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hineq : (D + 1) * N ≤ n + ((D + 1) * (N - 1) + 1) := by
    have := h5.trans (h1.trans (h2.trans (add_le_add le_rfl h3)))
    rw [← hn, ← Nat.cast_add, Nat.cast_le] at this
    exact this
  have hN : (D + 1) * N = (D + 1) * (N - 1) + (D + 1) := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := a.2; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hDn : D ≤ n := by
    rw [hN] at hineq
    generalize (D + 1) * (N - 1) = X at hineq
    omega
  obtain ⟨B, hB⟩ := M.exists_isBasis (Set.range r) (Set.subset_univ _)
  have hDB : ((D : ℕ) : ℕ∞) ≤ B.encard := by
    rw [hB.encard_eq_eRk, ← hn]
    exact_mod_cast hDn
  obtain ⟨B', hB'sub, hB'card⟩ := Set.exists_subset_encard_eq hDB
  have hB'fin : B'.Finite := Set.finite_of_encard_eq_coe hB'card
  refine ⟨hB'fin.toFinset, ?_, ?_, ?_⟩
  · have := Set.encard_coe_eq_coe_finsetCard hB'fin.toFinset
    rw [Set.Finite.coe_toFinset, hB'card] at this
    exact_mod_cast this.symm
  · rw [Set.Finite.coe_toFinset]
    exact hB'sub.trans hB.subset
  · rw [Set.Finite.coe_toFinset]
    exact AlgebraicIndependent.matroid_indep_iff.mp (hB.indep.subset hB'sub)
end Formalism.L2.Pj.CurveCount
