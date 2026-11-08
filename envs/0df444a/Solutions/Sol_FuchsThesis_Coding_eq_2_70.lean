-- Prove2me | solution 1 for FuchsThesis.Coding.eq_2_70
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:41:24.5932+00:00
-- url     : https://prove2.me/submissions/19f32173-20b9-46d4-bd0f-4811118b54d7

import Mathlib

namespace Aux_FuchsEq270

lemma term (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 < p → 0 < q) :
    0 ≤ (q - p) - (p * Real.log q - p * Real.log p) ∧
      ((q - p) - (p * Real.log q - p * Real.log p) = 0 → p = q) := by
  rcases hp.lt_or_eq with hp' | hp'
  · have hq' := hs hp'
    have hrw : p * Real.log q - p * Real.log p = p * Real.log (q / p) := by
      rw [Real.log_div hq'.ne' hp'.ne']; ring
    have hpq : p * (q / p - 1) = q - p := by field_simp
    rw [hrw]
    constructor
    · have := Real.log_le_sub_one_of_pos (div_pos hq' hp')
      nlinarith [mul_le_mul_of_nonneg_left this hp]
    · intro h
      by_contra hne
      have hne1 : q / p ≠ 1 := by
        intro h1; apply hne; field_simp at h1; linarith
      have := Real.log_lt_sub_one_of_pos (div_pos hq' hp') hne1
      have := mul_lt_mul_of_pos_left this hp'
      linarith
  · subst hp'
    simp only [zero_mul, sub_zero, sub_self]
    exact ⟨hq, fun h => h.symm⟩

end Aux_FuchsEq270

open Aux_FuchsEq270 in
theorem solution {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (hsupp : ∀ k, 0 < p k → 0 < q k) :
    (∑ k, p k * Real.log (q k) ≤ ∑ k, p k * Real.log (p k)) ∧
      (∑ k, p k * Real.log (q k) = ∑ k, p k * Real.log (p k) ↔ ∀ k, p k = q k) := by
  have hsum : ∑ k, ((q k - p k) - (p k * Real.log (q k) - p k * Real.log (p k)))
      = ∑ k, p k * Real.log (p k) - ∑ k, p k * Real.log (q k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp1, hq1]; ring
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ (q k - p k) - (p k * Real.log (q k) - p k * Real.log (p k)) :=
    fun k _ => (term (p k) (q k) (hp0 k) (hq0 k) (hsupp k)).1
  have h0 := Finset.sum_nonneg hnn
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hz : ∑ k, ((q k - p k) - (p k * Real.log (q k) - p k * Real.log (p k))) = 0 := by
      rw [hsum, h, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
    intro k
    exact (term (p k) (q k) (hp0 k) (hq0 k) (hsupp k)).2 (this k (Finset.mem_univ k))
  · have : p = q := funext h
    rw [this]
