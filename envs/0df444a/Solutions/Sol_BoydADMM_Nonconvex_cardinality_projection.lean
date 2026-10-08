-- Prove2me | solution 1 for BoydADMM.Nonconvex.cardinality_projection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:40:15.001465+00:00
-- url     : https://prove2.me/submissions/a817386b-dec6-4f46-af11-3c773dda8a12

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_ProjectionBasics



namespace BoydADMM.Nonconvex

lemma cp_split {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ i, f i = ∑ i, (if i ∈ S then 0 else f i) + ∑ i ∈ S, f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S) f]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, add_comm]
  congr 1
  · congr 1; ext i; simp

lemma cp_restrict_dist {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℝ) :
    sqDist (restrictTo I v) v = ∑ i, v i ^ 2 - ∑ i ∈ I, v i ^ 2 := by
  rw [cp_split I (fun i => v i ^ 2)]
  unfold sqDist restrictTo
  have : ∀ i, ((if i ∈ I then v i else 0) - v i) ^ 2 = if i ∈ I then 0 else v i ^ 2 := by
    intro i; split_ifs <;> ring
  simp_rw [this]; ring

lemma cp_dist_ge {n : ℕ} (x v : Fin n → ℝ) :
    ∑ i, v i ^ 2 - ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), v i ^ 2 ≤ sqDist x v := by
  rw [cp_split (Finset.univ.filter (fun i => x i ≠ 0)) (fun i => v i ^ 2)]
  unfold sqDist
  simp only [add_sub_cancel_right]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs with h
  · positivity
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
    rw [h]; ring_nf; rfl

lemma cp_top_sum {n : ℕ} (v : Fin n → ℝ) (I S : Finset (Fin n)) (hcard : S.card ≤ I.card)
    (hlargest : ∀ i ∈ I, ∀ j ∉ I, |v j| ≤ |v i|) :
    ∑ i ∈ S, v i ^ 2 ≤ ∑ i ∈ I, v i ^ 2 := by
  rw [← Finset.sum_inter_add_sum_sdiff S I, ← Finset.sum_inter_add_sum_sdiff I S,
    Finset.inter_comm]
  have hc : (S \ I).card ≤ (I \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S I
    have h2 := Finset.card_sdiff_add_card_inter I S
    rw [Finset.inter_comm] at h2
    omega
  have key : ∑ i ∈ S \ I, v i ^ 2 ≤ ∑ i ∈ I \ S, v i ^ 2 := by
    rcases (I \ S).eq_empty_or_nonempty with he | hne
    · have : S \ I = ∅ := by
        rw [he, Finset.card_empty] at hc
        exact Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
      rw [this, he]
    · set m := (I \ S).inf' hne (fun i => v i ^ 2)
      have hup : ∀ j ∈ S \ I, v j ^ 2 ≤ m := by
        intro j hj
        rw [Finset.le_inf'_iff]
        intro i hi
        have := hlargest i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
        rw [← sq_abs (v j), ← sq_abs (v i)]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have hlo : ∀ i ∈ I \ S, m ≤ v i ^ 2 := fun i hi => Finset.inf'_le _ hi
      have hm0 : 0 ≤ m := by
        rw [Finset.le_inf'_iff]; intro i _; positivity
      calc ∑ i ∈ S \ I, v i ^ 2 ≤ (S \ I).card • m := Finset.sum_le_card_nsmul _ _ _ hup
        _ ≤ (I \ S).card • m := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hm0
        _ ≤ ∑ i ∈ I \ S, v i ^ 2 := Finset.card_nsmul_le_sum _ _ _ hlo
  linarith

theorem card_proj_core {n : ℕ} (v : Fin n → ℝ) (c : ℕ)
    (I : Finset (Fin n))
    (hcard : I.card = min c n)
    (hlargest : ∀ i ∈ I, ∀ j ∉ I, |v j| ≤ |v i|) :
    restrictTo I v ∈ sparseSet c ∧
    ∀ x ∈ sparseSet c, sqDist (restrictTo I v) v ≤ sqDist x v := by
  refine ⟨?_, fun x hx => ?_⟩
  · show cardinality (restrictTo I v) ≤ c
    unfold cardinality restrictTo
    calc (Finset.univ.filter (fun i => (if i ∈ I then v i else 0) ≠ 0)).card ≤ I.card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          by_contra h; exact hi (if_neg h)
      _ ≤ c := by rw [hcard]; exact min_le_left _ _
  · have hx' : cardinality x ≤ c := hx
    unfold cardinality at hx'
    have hS : (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ I.card := by
      rw [hcard]
      refine le_min hx' ?_
      calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := Finset.card_fin n
    have := cp_top_sum v I _ hS hlargest
    have := cp_dist_ge x v
    rw [cp_restrict_dist]
    linarith

end BoydADMM.Nonconvex

open BoydADMM.Nonconvex


theorem solution {n : ℕ} (v : Fin n → ℝ) (c : ℕ)
    (I : Finset (Fin n))
    (hcard : I.card = min c n)
    (hlargest : ∀ i ∈ I, ∀ j ∉ I, |v j| ≤ |v i|) :
    restrictTo I v ∈ sparseSet c ∧
    ∀ x ∈ sparseSet c, sqDist (restrictTo I v) v ≤ sqDist x v := by
  exact card_proj_core v c I hcard hlargest
