-- Prove2me | solution 1 for BosonicLearn.displacementMatrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T18:44:42.187205+00:00
-- url     : https://prove2.me/submissions/99517a69-5b8d-4bb5-969d-4994572a2dd5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Theorems.Thm_BosonicLearn_displacementMatrix_mul

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

noncomputable section

/-- `D(−z)_{mn} = conj(D(z)_{nm})`. -/
private lemma disp_neg (z : ℂ) (m n : ℕ) :
    displacementMatrix (-z) m n = star (displacementMatrix z n m) := by
  unfold displacementMatrix
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, map_sum, Complex.normSq_neg,
    mul_comm (Nat.factorial n : ℝ) (Nat.factorial m : ℝ), min_comm n m]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_div₀, map_mul, map_pow, map_neg, map_natCast, Complex.conj_conj, neg_neg]
  ring

/-- `D(0)_{mn} = δ_{mn}`. -/
private lemma disp_zero (m n : ℕ) :
    displacementMatrix 0 m n = (if m = n then 1 else 0) := by
  unfold displacementMatrix
  by_cases h : m = n
  · subst h
    rw [if_pos rfl, min_self, Finset.sum_eq_single m]
    · have hm : Real.sqrt ((m.factorial : ℝ) * (m.factorial : ℝ)) = (m.factorial : ℝ) :=
        Real.sqrt_mul_self (Nat.cast_nonneg _)
      have f1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [hm]
      simp only [Complex.normSq_zero, neg_zero, zero_div, Real.exp_zero, one_mul, Nat.sub_self,
        pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, Complex.ofReal_natCast]
      field_simp
    · intro j hj hjm
      have hlt : j < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjm
      have hne : m - j ≠ 0 := by omega
      rw [zero_pow hne]
      simp
    · intro hm
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) hm
  · rw [if_neg h, Finset.sum_eq_zero, mul_zero]
    intro j hj
    have hj' : j ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : j ≤ m := le_trans hj' (min_le_left _ _)
    have h2 : j ≤ n := le_trans hj' (min_le_right _ _)
    rcases Nat.lt_or_ge j m with hlt | hge
    · have hne : m - j ≠ 0 := by omega
      rw [zero_pow hne]
      simp
    · have hne : n - j ≠ 0 := by omega
      rw [star_zero, neg_zero, zero_pow hne]
      simp

theorem solution (z : ℂ) (m n : ℕ) :
    displacementMatrix (-z) m n = star (displacementMatrix z n m) ∧
    displacementMatrix 0 m n = (if m = n then 1 else 0) ∧
    HasSum (fun k : ℕ => star (displacementMatrix z k m) * displacementMatrix z k n)
      (if m = n then 1 else 0) ∧
    HasSum (fun k : ℕ => displacementMatrix z m k * star (displacementMatrix z n k))
      (if m = n then 1 else 0) := by
  refine ⟨disp_neg z m n, disp_zero m n, ?_, ?_⟩
  · have h := (BosonicLearn.displacementMatrix_mul (-z) z m n).2
    have hfun : (fun k : ℕ => displacementMatrix (-z) m k * displacementMatrix z k n) =
        fun k : ℕ => star (displacementMatrix z k m) * displacementMatrix z k n := by
      funext k
      rw [disp_neg]
    have hval : Complex.exp ((-z * star z - star (-z) * z) / 2) * displacementMatrix (-z + z) m n =
        (if m = n then 1 else 0) := by
      have h0 : (-z * star z - star (-z) * z) / 2 = 0 := by
        rw [star_neg]
        ring
      rw [h0, Complex.exp_zero, one_mul, neg_add_cancel, disp_zero]
    rw [hfun, hval] at h
    exact h
  · have h := (BosonicLearn.displacementMatrix_mul z (-z) m n).2
    have hfun : (fun k : ℕ => displacementMatrix z m k * displacementMatrix (-z) k n) =
        fun k : ℕ => displacementMatrix z m k * star (displacementMatrix z n k) := by
      funext k
      rw [disp_neg]
    have hval : Complex.exp ((z * star (-z) - star z * -z) / 2) * displacementMatrix (z + -z) m n =
        (if m = n then 1 else 0) := by
      have h0 : (z * star (-z) - star z * -z) / 2 = 0 := by
        rw [star_neg]
        ring
      rw [h0, Complex.exp_zero, one_mul, add_neg_cancel, disp_zero]
    rw [hfun, hval] at h
    exact h
