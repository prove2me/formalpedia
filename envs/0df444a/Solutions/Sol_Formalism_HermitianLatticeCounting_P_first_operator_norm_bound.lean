-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.first_operator_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:34.796905+00:00
-- url     : https://prove2.me/submissions/91eb8eca-6ea7-4907-a1b1-e1968d9fc216

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_le_exp_mul_of_near_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_paired_sum_exp_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_half_integer_neg_le_neg_half
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_abs_of_int_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.supL2RatioMajorant := by
  intro k M lam mu u b bv ga q0 s hk hM hyp hreg
  obtain ⟨hlam, hlamZ, hluZ, hlu1, hlu2, hcloud, hnode, hlamb, hub, hgap, hga, hmuZ, hmu, hsum, hq1, hq2, hq3⟩ := hyp
  have hδ0 : ∀ a, 0 ≤ |mu a - lam a| := fun a => abs_nonneg _
  have hδq : ∀ a, |mu a - lam a| ≤ q0 := fun a =>
    le_trans (Finset.single_le_sum (f := fun a => |mu a - lam a|) (fun a _ => hδ0 a) (mem_univ a)) hsum
  have hq0 : 0 ≤ q0 := le_trans (hδ0 s) (hδq s)
  have hmu1 : ∀ a, mu a ≤ lam a + |mu a - lam a| := fun a => by
    have := le_abs_self (mu a - lam a); linarith
  have hmu2 : ∀ a, lam a - |mu a - lam a| ≤ mu a := fun a => by
    have := neg_abs_le (mu a - lam a); linarith
  have F1 : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) = (i : ℕ) → lam a + 1 / 2 ≤ u i := by
    intro i a h
    have e : a = Fin.castAdd M i := Fin.ext h
    obtain ⟨z, hz⟩ := hluZ a i
    have := half_integer_neg_le_neg_half _ z hz (by rw [e]; linarith [hlu1 i])
    linarith
  have F2 : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) + 1 = (i : ℕ) → u i + 1 / 2 ≤ lam a := by
    intro i a h
    have ha : (a : ℕ) < k := by have := i.isLt; omega
    have e : a = Fin.castAdd M ⟨(a : ℕ), ha⟩ := Fin.ext rfl
    obtain ⟨z, hz⟩ := hluZ a i
    have h1 : u i < lam a := by rw [e]; exact hlu2 ⟨(a : ℕ), ha⟩ i h
    have := half_integer_neg_le_neg_half (u i - lam a) (-z - 1) (by push_cast; linarith) (by linarith)
    linarith

  have hbv : 1 ≤ bv := by
    have h1 := hnode ⟨k - 1, by omega⟩ (by simp; omega)
    have h2 := hnode ⟨k, by omega⟩ (by simp)
    obtain ⟨z, hz⟩ := hlamZ ⟨k - 1, by omega⟩ ⟨k, by omega⟩
    have h3 : lam ⟨k, by omega⟩ < lam ⟨k - 1, by omega⟩ := hlam (by simp [Fin.lt_def]; omega)
    have h4 := one_le_abs_of_int_ne_zero _ z hz (by linarith)
    rw [abs_of_pos (by linarith)] at h4
    linarith [h1.2, h2.1]
  have hb : 1 ≤ b := by
    have h1 := hnode ⟨k, by omega⟩ (by simp)
    have h2 := abs_le.mp (hlamb ⟨k, by omega⟩)
    linarith [h1.2, h2.1]
  have hD : ∀ a ∈ univ.erase s, 1 ≤ |mu s - 1 - mu a| := by
    intro a ha
    have hne := Finset.ne_of_mem_erase ha
    obtain ⟨z1, hz1⟩ := hmuZ s
    obtain ⟨z2, hz2⟩ := hlamZ s a
    obtain ⟨z3, hz3⟩ := hmuZ a
    apply one_le_abs_of_int_ne_zero _ (z1 + z2 - z3 - 1) (by push_cast; linarith)
    exact sub_ne_zero.mpr (hreg a hne)
  have hN : ∀ i : Fin k, |mu s - 1 / 2 - u i| ≤ 4 * b := by
    intro i
    have h1 := abs_le.mp (hlamb s)
    have h2 := abs_le.mp (hub i)
    have h3 := hmu1 s
    have h4 := hmu2 s
    have h5 := hδq s
    rw [abs_le]; constructor <;> linarith
  have hDpos : 0 < ∏ a ∈ univ.erase s, |mu s - 1 - mu a| :=
    Finset.prod_pos fun a ha => lt_of_lt_of_le one_pos (hD a ha)
  have hsumle : ∀ c : ℝ, 0 < c → ∑ a ∈ univ.erase s, 2 * |mu a - lam a| / c ≤ 2 * q0 / c := by
    intro c hc
    calc ∑ a ∈ univ.erase s, 2 * |mu a - lam a| / c ≤ ∑ a, 2 * |mu a - lam a| / c :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => by positivity)
      _ = 2 * (∑ a, |mu a - lam a|) / c := by rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ 2 * q0 / c := by gcongr
  rw [div_le_iff₀ hDpos]
  by_cases hs : (s : ℕ) + 1 < k
  · rw [if_pos hs]
    have above : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) + 1 = (i : ℕ) → (i : ℕ) < (s : ℕ) →
        |mu s - 1 / 2 - u i| ≤ Real.exp (2 * |mu a - lam a| / (ga / 2)) * |mu s - 1 - mu a| := by
      intro i a hai his
      have g1 := hgap ⟨(i : ℕ), by have := i.isLt; omega⟩ s (by simp [Fin.lt_def]; exact his) hs
      have f1 := F1 i ⟨(i : ℕ), by have := i.isLt; omega⟩ rfl
      have f2 := F2 i a hai
      have h3 := hmu1 s
      have h5 := hδq s
      have h6 := hδq a
      have h7 := hmu2 a
      apply le_exp_mul_of_near_bound _ _ (lam a + 1 - mu s) _ _
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have := neg_le_abs (mu s - 1 - mu a); linarith
      · linarith
      · linarith
      · exact hδ0 a
      · linarith
    have below : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) = (i : ℕ) → (s : ℕ) + 2 ≤ (i : ℕ) →
        |mu s - 1 / 2 - u i| ≤ Real.exp (2 * |mu a - lam a| / (ga / 2)) * |mu s - 1 - mu a| := by
      intro i a hai his
      have g1 := hgap s ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ (by simp [Fin.lt_def]; omega)
        (by have := i.isLt; simp; omega)
      have f1 := F1 i a hai
      have f2 := F2 i ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ (by simp; omega)
      have h3 := hmu2 s
      have h5 := hδq s
      have h6 := hδq a
      have h7 := hmu1 a
      apply le_exp_mul_of_near_bound _ _ (mu s - 1 - lam a) _ _
      · rw [abs_of_nonneg (by linarith)]; linarith
      · have := le_abs_self (mu s - 1 - mu a); linarith
      · linarith
      · linarith
      · exact hδ0 a
      · linarith
    have key := paired_sum_exp_bound (univ : Finset (Fin k))
      (univ.filter fun i : Fin k => (1 ≤ (i : ℕ) ∧ (i : ℕ) < (s : ℕ)) ∨ (s : ℕ) + 2 ≤ (i : ℕ))
      (univ.erase s) (fun i => |mu s - 1 / 2 - u i|) (fun a => |mu s - 1 - mu a|)
      (fun a => 2 * |mu a - lam a| / (ga / 2))
      (fun i => ⟨if (i : ℕ) < (s : ℕ) then (i : ℕ) - 1 else (i : ℕ), by
        have := i.isLt; split_ifs <;> omega⟩) (4 * b) 3 (Finset.subset_univ _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        apply Finset.mem_erase.mpr ⟨?_, mem_univ _⟩
        intro e
        have e' := congrArg Fin.val e
        simp only at e'
        split_ifs at e' <;> omega)
      (by
        intro i hi j hj e
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        have e' := congrArg Fin.val e
        simp only at e'
        apply Fin.ext
        split_ifs at e' <;> omega)
      (fun i _ => abs_nonneg _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        by_cases c : (i : ℕ) < (s : ℕ)
        · apply above i _ _ c
          simp only [c, if_true]; omega
        · apply below i _ _ (by omega)
          simp only [c, if_false])
      (fun i _ => hN i) (by linarith)
      (by
        have hsub : (univ : Finset (Fin k)) \
            (univ.filter fun i : Fin k => (1 ≤ (i : ℕ) ∧ (i : ℕ) < (s : ℕ)) ∨ (s : ℕ) + 2 ≤ (i : ℕ)) ⊆
            {(⟨0, by omega⟩ : Fin k), ⟨(s : ℕ), by omega⟩, ⟨(s : ℕ) + 1, hs⟩} := by
          intro i hi
          have h := (Finset.mem_sdiff.mp hi).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_three)
      hD (fun a _ => by positivity)
    have hS := hsumle (ga / 2) (by linarith)
    have hS2 : 2 * q0 / (ga / 2) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hexp : Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (ga / 2)) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (le_trans hS hS2)
    have hsq : 1 ≤ Real.sqrt k := by
      rw [Real.one_le_sqrt]; exact_mod_cast hk
    calc ∏ i, |mu s - 1 / 2 - u i|
        ≤ (4 * b) ^ 3 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (ga / 2)) *
          ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := key
      _ ≤ 64 * Real.exp 1 * Real.sqrt k * b ^ 3 * ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := by
          apply mul_le_mul_of_nonneg_right _ hDpos.le
          have h1 : (4 * b) ^ 3 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (ga / 2)) ≤
              (4 * b) ^ 3 * Real.exp 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
          have h2 : (4 * b) ^ 3 * Real.exp 1 * 1 ≤ (4 * b) ^ 3 * Real.exp 1 * Real.sqrt k :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          calc _ ≤ (4 * b) ^ 3 * Real.exp 1 * Real.sqrt k := by linarith
            _ = 64 * Real.exp 1 * Real.sqrt k * b ^ 3 := by ring
  · rw [if_neg hs]
    have above : ∀ (i : Fin k) (a : Fin (k + M)), (a : ℕ) + 1 = (i : ℕ) → (i : ℕ) + 1 < k →
        |mu s - 1 / 2 - u i| ≤ Real.exp (2 * |mu a - lam a| / (bv / 2)) * |mu s - 1 - mu a| := by
      intro i a hai hik
      have g1 := hcloud ⟨(i : ℕ), by have := i.isLt; omega⟩ hik
      have g2 := hnode s (by omega)
      have f1 := F1 i ⟨(i : ℕ), by have := i.isLt; omega⟩ rfl
      have f2 := F2 i a hai
      have h3 := hmu1 s
      have h5 := hδq s
      have h6 := hδq a
      have h7 := hmu2 a
      apply le_exp_mul_of_near_bound _ _ (lam a + 1 - mu s) _ _
      · rw [abs_of_nonpos (by linarith [g1.1, g2.2])]; linarith
      · have := neg_le_abs (mu s - 1 - mu a); linarith
      · linarith
      · linarith [g1.1, g2.2]
      · exact hδ0 a
      · linarith [g1.1, g2.2]
    have key := paired_sum_exp_bound (univ : Finset (Fin k))
      (univ.filter fun i : Fin k => 1 ≤ (i : ℕ) ∧ (i : ℕ) + 1 < k)
      (univ.erase s) (fun i => |mu s - 1 / 2 - u i|) (fun a => |mu s - 1 - mu a|)
      (fun a => 2 * |mu a - lam a| / (bv / 2))
      (fun i => ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩) (4 * b) 2 (Finset.subset_univ _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        apply Finset.mem_erase.mpr ⟨?_, mem_univ _⟩
        intro e
        have e' := congrArg Fin.val e
        simp only at e'
        omega)
      (by
        intro i hi j hj e
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        have e' := congrArg Fin.val e
        simp only at e'
        apply Fin.ext
        omega)
      (fun i _ => abs_nonneg _)
      (by
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        apply above i _ _ h.2
        simp only; omega)
      (fun i _ => hN i) (by linarith)
      (by
        have hsub : (univ : Finset (Fin k)) \
            (univ.filter fun i : Fin k => 1 ≤ (i : ℕ) ∧ (i : ℕ) + 1 < k) ⊆
            {(⟨0, by omega⟩ : Fin k), ⟨k - 1, by omega⟩} := by
          intro i hi
          have h := (Finset.mem_sdiff.mp hi).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          have := i.isLt
          omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two)
      hD (fun a _ => by positivity)
    have hS := hsumle (bv / 2) (by linarith)
    have hS2 : 2 * q0 / (bv / 2) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hexp : Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (bv / 2)) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (le_trans hS hS2)
    calc ∏ i, |mu s - 1 / 2 - u i|
        ≤ (4 * b) ^ 2 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (bv / 2)) *
          ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := key
      _ ≤ 16 * Real.exp 1 * b ^ 2 * ∏ a ∈ univ.erase s, |mu s - 1 - mu a| := by
          apply mul_le_mul_of_nonneg_right _ hDpos.le
          have h1 : (4 * b) ^ 2 * Real.exp (∑ a ∈ univ.erase s, 2 * |mu a - lam a| / (bv / 2)) ≤
              (4 * b) ^ 2 * Real.exp 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
          calc _ ≤ (4 * b) ^ 2 * Real.exp 1 := h1
            _ = 16 * Real.exp 1 * b ^ 2 := by ring
end Formalism.HermitianLatticeCounting.P
