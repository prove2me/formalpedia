-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.lopsided_cut_weak_form_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:07:49.517213+00:00
-- url     : https://prove2.me/submissions/af09e981-03c3-49db-98f8-eb2fdf4bb18b

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic



namespace Disjunctive.MonoidalStrengthening

theorem lopB_core {q n : ℕ} [Nonempty (Fin q)]
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n)) (k : Fin q)
    (ha0 : ∀ i, 0 < a0 i) (hb : ∀ i, b i ≤ a0 i)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    1 ≤ ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j := by
  classical
  have hbeta : ∀ i j, a i j / a0 i ≤ BetaJUnstrengthened a a0 j := by
    intro i j
    unfold BetaJUnstrengthened
    exact Finset.le_sup' (fun i => a i j / a0 i) (Finset.mem_univ i)
  -- rewrite the objective as a sum over univ
  let d : Fin n → ℝ := fun j => if j ∈ J1 then
    min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) else BetaJUnstrengthened a a0 j
  have hobj : ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j = ∑ j, d j * x j := by
    rw [← Finset.sum_sdiff (Finset.subset_univ J1) (f := fun j => d j * x j)]
    conv_rhs => rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl; intro j hj; simp [d, hj]
    · apply Finset.sum_congr rfl; intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      simp [d, hj]
  rw [hobj]
  have hk0 := ha0 k
  by_cases hsel : ∃ j, (j ∈ J1 ∧ (a k j + a0 k - b k) / a0 k ≤ BetaJUnstrengthened a a0 j) ∧ x j ≠ 0
  · obtain ⟨j0, ⟨hj0J, hj0le⟩, hj0x⟩ := hsel
    obtain ⟨m0, hm0⟩ := hx_int j0 hj0J
    have hxj0 : 1 ≤ x j0 := by
      have hpos : 0 < x j0 := lt_of_le_of_ne (hx_nonneg j0) (Ne.symm hj0x)
      rw [hm0] at hpos ⊢
      have : (0:ℤ) < m0 := by exact_mod_cast hpos
      exact_mod_cast this
    let ind : Fin n → ℝ := fun j =>
      if j ∈ J1 ∧ (a k j + a0 k - b k) / a0 k ≤ BetaJUnstrengthened a a0 j then x j else 0
    have hper : ∀ j, (a k j * x j + (a0 k - b k) * ind j) / a0 k ≤ d j * x j := by
      intro j
      have hxj := hx_nonneg j
      simp only [ind, d]
      by_cases hJ : j ∈ J1
      · by_cases hle : (a k j + a0 k - b k) / a0 k ≤ BetaJUnstrengthened a a0 j
        · rw [if_pos ⟨hJ, hle⟩, if_pos hJ, min_eq_left hle]
          apply le_of_eq; field_simp; ring
        · rw [if_neg (fun h => hle h.2), if_pos hJ, min_eq_right (le_of_not_ge hle)]
          rw [mul_zero, add_zero, mul_div_right_comm]
          exact mul_le_mul_of_nonneg_right (hbeta k j) hxj
      · rw [if_neg (fun h => hJ h.1), if_neg hJ, mul_zero, add_zero, mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right (hbeta k j) hxj
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hind : 1 ≤ ∑ j, ind j := by
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ ind j := by
        intro j _; simp only [ind]; split_ifs
        · exact hx_nonneg j
        · exact le_rfl
      have := Finset.single_le_sum hnn (Finset.mem_univ j0)
      have : ind j0 = x j0 := by simp [ind, hj0J, hj0le]
      linarith
    have hD : 0 ≤ a0 k - b k := by linarith [hb k]
    have hlb := hx_lb k
    have : 1 ≤ (∑ j, a k j * x j + (a0 k - b k) * ∑ j, ind j) / a0 k := by
      rw [le_div_iff₀ hk0]; nlinarith
    linarith
  · push_neg at hsel
    obtain ⟨i, hi⟩ := hx_disj
    have hper : ∀ j, a i j * x j / a0 i ≤ d j * x j := by
      intro j
      have hxj := hx_nonneg j
      have hB : a i j * x j / a0 i ≤ BetaJUnstrengthened a a0 j * x j := by
        rw [mul_div_right_comm]; exact mul_le_mul_of_nonneg_right (hbeta i j) hxj
      simp only [d]
      by_cases hJ : j ∈ J1
      · rw [if_pos hJ]
        by_cases hle : (a k j + a0 k - b k) / a0 k ≤ BetaJUnstrengthened a a0 j
        · have := hsel j ⟨hJ, hle⟩
          rw [this]; simp
        · rw [min_eq_right (le_of_not_ge hle)]; exact hB
      · rw [if_neg hJ]; exact hB
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
    rw [← Finset.sum_div] at hsum
    have : 1 ≤ (∑ j, a i j * x j) / a0 i := by rw [le_div_iff₀ (ha0 i)]; linarith
    linarith

end Disjunctive.MonoidalStrengthening

open Disjunctive.MonoidalStrengthening


theorem solution {q n : ℕ} [Nonempty (Fin q)]
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n)) (k : Fin q)
    (ha0 : ∀ i, 0 < a0 i) (hb : ∀ i, b i ≤ a0 i)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    1 ≤ ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j := by
  exact lopB_core a a0 b J1 k ha0 hb x hx_nonneg hx_int hx_lb hx_disj
