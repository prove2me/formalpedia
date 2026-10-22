-- Prove2me | solution 1 for CompOT.EntropicLimit.entropy_max_at_product
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:59:57.333802+00:00
-- url     : https://prove2.me/submissions/f860da71-584b-4bdb-8e84-380780348aee

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs
set_option autoImplicit false
open CompOT.EntropicLimit

lemma ss_le_row {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ} {R : Matrix (Fin n) (Fin m) ℝ}
    (hR : R ∈ CompOT.Assignment.couplings a b) (i : Fin n) (j : Fin m) : R i j ≤ a i := by
  obtain ⟨h0, hr, hc⟩ := hR
  rw [← hr i]
  exact Finset.single_le_sum (f := fun j => R i j) (fun j _ => h0 i j) (Finset.mem_univ j)

lemma ss_le_col {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ} {R : Matrix (Fin n) (Fin m) ℝ}
    (hR : R ∈ CompOT.Assignment.couplings a b) (i : Fin n) (j : Fin m) : R i j ≤ b j := by
  obtain ⟨h0, hr, hc⟩ := hR
  rw [← hc j]
  exact Finset.single_le_sum (f := fun i => R i j) (fun i _ => h0 i j) (Finset.mem_univ i)

lemma ss_sum_log {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ} {R : Matrix (Fin n) (Fin m) ℝ}
    (hR : R ∈ CompOT.Assignment.couplings a b) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    ∑ i, ∑ j, R i j * Real.log (a i * b j) =
      ∑ i, a i * Real.log (a i) + ∑ j, b j * Real.log (b j) := by
  have hpt : ∀ i j, R i j * Real.log (a i * b j) = R i j * Real.log (a i) + R i j * Real.log (b j) := by
    intro i j
    have h0 : 0 ≤ R i j := hR.1 i j
    by_cases hai : a i = 0
    · have : R i j = 0 := le_antisymm (hai ▸ ss_le_row hR i j) h0
      simp [this]
    by_cases hbj : b j = 0
    · have : R i j = 0 := le_antisymm (hbj ▸ ss_le_col hR i j) h0
      simp [this]
    rw [Real.log_mul hai hbj]; ring
  simp_rw [hpt]
  simp only [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hR.2.1 i]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hR.2.2 j]

lemma ss_total {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ} {R : Matrix (Fin n) (Fin m) ℝ}
    (hR : R ∈ CompOT.Assignment.couplings a b) : ∑ i, ∑ j, R i j = ∑ i, a i := by
  refine Finset.sum_congr rfl fun i _ => hR.2.1 i

theorem solution {n m : ℕ}
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (Matrix.of fun i j => a i * b j) ∈ CompOT.Assignment.couplings a b ∧
      ∀ Q ∈ CompOT.Assignment.couplings a b, Q ≠ (Matrix.of fun i j => a i * b j) →
        entropy Q < entropy (Matrix.of fun i j => a i * b j) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hK : (Matrix.of fun i j => a i * b j) ∈ CompOT.Assignment.couplings a b := by
    refine ⟨fun i j => mul_nonneg (ha0 i) (hb0 j), fun i => ?_, fun j => ?_⟩
    · simp only [Matrix.of_apply]; rw [← Finset.mul_sum, hb1, mul_one]
    · simp only [Matrix.of_apply]; rw [← Finset.sum_mul, ha1, one_mul]
  refine ⟨hK, fun Q hQ hne => ?_⟩
  set K : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => a i * b j with hKdef
  have hKij : ∀ i j, K i j = a i * b j := fun i j => rfl
  -- pointwise inequality
  have hpt : ∀ i j, Q i j - K i j ≤ Q i j * Real.log (Q i j) - Q i j * Real.log (K i j) ∧
      (Q i j ≠ K i j → Q i j - K i j < Q i j * Real.log (Q i j) - Q i j * Real.log (K i j)) := by
    intro i j
    have hq0 : 0 ≤ Q i j := hQ.1 i j
    have hk0 : 0 ≤ K i j := mul_nonneg (ha0 i) (hb0 j)
    rcases hq0.lt_or_eq with hqpos | hqz
    · have hkpos : 0 < K i j := by
        rw [hKij]
        refine mul_pos ?_ ?_
        · exact lt_of_lt_of_le hqpos (ss_le_row hQ i j)
        · exact lt_of_lt_of_le hqpos (ss_le_col hQ i j)
      have hlog : Real.log (K i j / Q i j) = Real.log (K i j) - Real.log (Q i j) :=
        Real.log_div hkpos.ne' hqpos.ne'
      have hxpos : 0 < K i j / Q i j := div_pos hkpos hqpos
      have hle := Real.log_le_sub_one_of_pos hxpos
      rw [hlog] at hle
      have e : Q i j * (K i j / Q i j - 1) = K i j - Q i j := by field_simp
      have hm := mul_le_mul_of_nonneg_left hle hqpos.le
      rw [e] at hm
      refine ⟨by nlinarith [hm], fun hne' => ?_⟩
      have hx1 : K i j / Q i j ≠ 1 := by
        intro h; apply hne'; field_simp at h; exact h.symm
      have hlt := Real.log_lt_sub_one_of_pos hxpos hx1
      rw [hlog] at hlt
      have hm' := mul_lt_mul_of_pos_left hlt hqpos
      rw [e] at hm'
      nlinarith [hm']
    · rw [← hqz]
      simp only [zero_mul, sub_zero, zero_sub]
      refine ⟨by linarith, fun hne' => ?_⟩
      have : 0 < K i j := lt_of_le_of_ne hk0 hne'
      linarith
  -- sums
  have hsumlogK := ss_sum_log hK ha0 hb0
  have hsumlogQ := ss_sum_log hQ ha0 hb0
  have hKK : ∑ i, ∑ j, K i j * Real.log (K i j) = ∑ i, ∑ j, Q i j * Real.log (K i j) := by
    have e1 : ∑ i, ∑ j, K i j * Real.log (K i j) = ∑ i, ∑ j, K i j * Real.log (a i * b j) := rfl
    rw [e1, hsumlogK]
    have e2 : ∑ i, ∑ j, Q i j * Real.log (K i j) = ∑ i, ∑ j, Q i j * Real.log (a i * b j) := rfl
    rw [e2, hsumlogQ]
  have htot : ∑ i, ∑ j, K i j = ∑ i, ∑ j, Q i j := by
    rw [ss_total hK, ss_total hQ]
  -- strictness
  have hlt : ∑ i, ∑ j, (Q i j - K i j) <
      ∑ i, ∑ j, (Q i j * Real.log (Q i j) - Q i j * Real.log (K i j)) := by
    obtain ⟨i0, j0, hij⟩ : ∃ i j, Q i j ≠ K i j := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hne (by ext i j; exact hcon i j)
    refine Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => (hpt i j).1) ⟨i0, Finset.mem_univ _, ?_⟩
    exact Finset.sum_lt_sum (fun j _ => (hpt i0 j).1) ⟨j0, Finset.mem_univ _, (hpt i0 j0).2 hij⟩
  have hzero : ∑ i, ∑ j, (Q i j - K i j) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [htot]; ring
  unfold entropy
  simp only [Real.negMulLog, Finset.sum_add_distrib]
  simp only [neg_mul, Finset.sum_neg_distrib]
  simp only [Finset.sum_sub_distrib] at hlt hzero
  rw [← hKK] at hlt
  linarith
