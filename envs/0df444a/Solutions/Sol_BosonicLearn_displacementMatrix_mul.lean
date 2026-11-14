-- Prove2me | solution 1 for BosonicLearn.displacementMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T18:42:45.052216+00:00
-- url     : https://prove2.me/submissions/a620d70f-30c6-47d9-aa74-aa9dd51d590f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

noncomputable section

/-! ### The unnormalised two-variable matrix element -/

/-- `E2 x y m n = ∑_{j ≤ min m n} x^(m-j) y^(n-j) / (j! (m-j)! (n-j)!)`; the displacement matrix is
`e^{-|z|²/2} √(m! n!) · E2 z (-z̄) m n`. -/
private def E2 (x y : ℂ) (m n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (min m n + 1),
    x ^ (m - j) * y ^ (n - j) /
      ((Nat.factorial j : ℂ) * (Nat.factorial (m - j) : ℂ) * (Nat.factorial (n - j) : ℂ))

/-- The summand of `E2`, extended by zero outside `j ≤ min m n`. -/
private def T2 (x y : ℂ) (m n j : ℕ) : ℂ :=
  if j ≤ m ∧ j ≤ n then
    x ^ (m - j) * y ^ (n - j) /
      ((Nat.factorial j : ℂ) * (Nat.factorial (m - j) : ℂ) * (Nat.factorial (n - j) : ℂ))
  else 0

private lemma E2_eq_sum_T2 (x y : ℂ) (m n N : ℕ) (hN : min m n + 1 ≤ N) :
    E2 x y m n = ∑ j ∈ Finset.range N, T2 x y m n j := by
  calc E2 x y m n = ∑ j ∈ Finset.range (min m n + 1), T2 x y m n j := by
        unfold E2
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [T2, if_pos ⟨le_trans hj' (min_le_left _ _), le_trans hj' (min_le_right _ _)⟩]
    _ = ∑ j ∈ Finset.range N, T2 x y m n j := by
        refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun j _ hj => ?_
        have hneg : ¬ (j ≤ m ∧ j ≤ n) := by
          rintro ⟨h1, h2⟩
          exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min h1 h2)))
        rw [T2, if_neg hneg]

private lemma T2_succ (x y : ℂ) (m k j : ℕ) :
    ((m : ℂ) + 1) * T2 x y (m + 1) (k + 1) (j + 1) =
      T2 x y m k j + x * T2 x y m (k + 1) (j + 1) := by
  unfold T2
  by_cases hjk : j ≤ k
  · rcases lt_trichotomy j m with h | h | h
    · obtain ⟨d, rfl⟩ : ∃ d, m = j + 1 + d := ⟨m - (j + 1), by omega⟩
      obtain ⟨e, rfl⟩ : ∃ e, k = j + e := ⟨k - j, by omega⟩
      have h1 : j + 1 + d + 1 - (j + 1) = d + 1 := by omega
      have h2 : j + e + 1 - (j + 1) = e := by omega
      have h3 : j + 1 + d - j = d + 1 := by omega
      have h4 : j + e - j = e := by omega
      have h5 : j + 1 + d - (j + 1) = d := by omega
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩,
        h1, h2, h3, h4, h5]
      simp only [Nat.factorial_succ]
      push_cast
      have f1 : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f2 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f3 : ((e.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f4 : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      have f5 : ((d : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero d
      field_simp
      ring
    · subst h
      obtain ⟨e, rfl⟩ : ∃ e, k = j + e := ⟨k - j, by omega⟩
      have h1 : j + 1 - (j + 1) = 0 := by omega
      have h2 : j + e + 1 - (j + 1) = e := by omega
      have h3 : j - j = 0 := by omega
      have h4 : j + e - j = e := by omega
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_neg (by omega),
        h1, h2, h3, h4]
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      have f1 : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f3 : ((e.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f4 : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      field_simp
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

private lemma T2_zero_succ (x y : ℂ) (m k : ℕ) :
    ((m : ℂ) + 1) * T2 x y (m + 1) (k + 1) 0 = x * T2 x y m (k + 1) 0 := by
  unfold T2
  rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩]
  simp only [Nat.sub_zero, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  have f1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have f5 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  field_simp
  ring

/-- Row recursion, `k ≥ 1`. -/
private lemma E2_row_succ (x y : ℂ) (m k : ℕ) :
    ((m : ℂ) + 1) * E2 x y (m + 1) (k + 1) = E2 x y m k + x * E2 x y m (k + 1) := by
  have e1 := E2_eq_sum_T2 x y (m + 1) (k + 1) (m + k + 2 + 1) (by omega)
  have e2 := E2_eq_sum_T2 x y m k (m + k + 2) (by omega)
  have e3 := E2_eq_sum_T2 x y m (k + 1) (m + k + 2 + 1) (by omega)
  rw [Finset.sum_range_succ'] at e1 e3
  rw [e1, e2, e3, mul_add, Finset.mul_sum, mul_add, Finset.mul_sum, T2_zero_succ, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => T2_succ x y m k j

private lemma E2_zero_right (x y : ℂ) (m : ℕ) : E2 x y m 0 = x ^ m / (m.factorial : ℂ) := by
  simp [E2]

private lemma E2_zero_left (x y : ℂ) (n : ℕ) : E2 x y 0 n = y ^ n / (n.factorial : ℂ) := by
  simp [E2]

/-- Row recursion, `k = 0`. -/
private lemma E2_row_zero (x y : ℂ) (m : ℕ) :
    ((m : ℂ) + 1) * E2 x y (m + 1) 0 = x * E2 x y m 0 := by
  rw [E2_zero_right, E2_zero_right, Nat.factorial_succ]
  push_cast
  have f1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  field_simp
  ring

private lemma E2_symm (x y : ℂ) (m n : ℕ) : E2 x y m n = E2 y x n m := by
  unfold E2
  rw [min_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma E2_col_succ (x y : ℂ) (k n : ℕ) :
    ((n : ℂ) + 1) * E2 x y (k + 1) (n + 1) = E2 x y k n + y * E2 x y (k + 1) n := by
  rw [E2_symm x y (k + 1) (n + 1), E2_symm x y k n, E2_symm x y (k + 1) n]
  exact E2_row_succ y x n k

/-! ### Absolutely convergent series -/

private def AHS (f : ℕ → ℂ) (v : ℂ) : Prop := Summable (fun k => ‖f k‖) ∧ HasSum f v

private lemma AHS_add {f g : ℕ → ℂ} {v w : ℂ} (hf : AHS f v) (hg : AHS g w) :
    AHS (fun k => f k + g k) (v + w) :=
  ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _) (hf.1.add hg.1),
    hf.2.add hg.2⟩

private lemma AHS_const_mul {f : ℕ → ℂ} {v : ℂ} (c : ℂ) (hf : AHS f v) :
    AHS (fun k => c * f k) (c * v) :=
  ⟨by simpa [norm_mul] using hf.1.mul_left ‖c‖, hf.2.mul_left c⟩

private lemma AHS_shift {f : ℕ → ℂ} {v : ℂ} (hf : AHS f v) :
    AHS (fun k => f (k + 1)) (v - f 0) :=
  ⟨(summable_nat_add_iff 1 (f := fun k => ‖f k‖)).mpr hf.1, by
    have := (hasSum_nat_add_iff' 1).mpr hf.2
    simpa using this⟩

private lemma AHS_of_succ {f : ℕ → ℂ} {v : ℂ} (hf : AHS (fun k => f (k + 1)) v) :
    AHS f (f 0 + v) :=
  ⟨(summable_nat_add_iff 1 (f := fun k => ‖f k‖)).mp hf.1, hf.2.zero_add⟩

/-- The induction step used twice below: a series whose shifted `c`-multiple is known. -/
private lemma AHS_step {g f : ℕ → ℂ} {v w c : ℂ} (hc : c ≠ 0) (hf : AHS f v)
    (hfun : ∀ k, c * g (k + 1) = f k) (hval : c * g 0 + v = c * w) : AHS g w := by
  have h1 : AHS (fun k => c * g (k + 1)) v := by
    have : (fun k => c * g (k + 1)) = f := funext hfun
    rw [this]; exact hf
  have h2 : AHS (fun k => c * g k) (c * g 0 + v) := AHS_of_succ (f := fun k => c * g k) h1
  have h3 : AHS (fun k => c⁻¹ * (c * g k)) (c⁻¹ * (c * g 0 + v)) := AHS_const_mul c⁻¹ h2
  have e1 : (fun k => c⁻¹ * (c * g k)) = g := funext fun k => inv_mul_cancel_left₀ hc _
  have e2 : c⁻¹ * (c * g 0 + v) = w := by rw [hval, inv_mul_cancel_left₀ hc]
  rw [e1, e2] at h3
  exact h3

/-! ### Column generating function -/

private lemma E2_genfun (x y s : ℂ) (n : ℕ) :
    AHS (fun k => s ^ k * E2 x y k n)
      (Complex.exp (x * s) * (s + y) ^ n / (n.factorial : ℂ)) := by
  induction n with
  | zero =>
    have h1 : (fun k => s ^ k * E2 x y k 0) = fun k => (x * s) ^ k / (k.factorial : ℂ) := by
      funext k
      rw [E2_zero_right, mul_pow]
      ring
    rw [h1]
    refine ⟨NormedSpace.norm_expSeries_div_summable (x * s), ?_⟩
    have := NormedSpace.expSeries_div_hasSum_exp (x * s)
    rw [← Complex.exp_eq_exp_ℂ] at this
    simpa using this
  | succ n ih =>
    have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hstep := AHS_add (AHS_const_mul s ih) (AHS_const_mul y (AHS_shift ih))
    refine AHS_step (c := (n : ℂ) + 1) hn hstep (fun k => ?_) ?_
    · have r := E2_col_succ x y k n
      show ((n : ℂ) + 1) * (s ^ (k + 1) * E2 x y (k + 1) (n + 1)) =
        s * (s ^ k * E2 x y k n) + y * (s ^ (k + 1) * E2 x y (k + 1) n)
      linear_combination s ^ (k + 1) * r
    · show ((n : ℂ) + 1) * (s ^ 0 * E2 x y 0 (n + 1)) +
        (s * (Complex.exp (x * s) * (s + y) ^ n / (n.factorial : ℂ)) +
          y * (Complex.exp (x * s) * (s + y) ^ n / (n.factorial : ℂ) - s ^ 0 * E2 x y 0 n)) =
        ((n : ℂ) + 1) * (Complex.exp (x * s) * (s + y) ^ (n + 1) / ((n + 1).factorial : ℂ))
      rw [E2_zero_left, E2_zero_left, Nat.factorial_succ]
      push_cast
      have f1 : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
      ring

/-! ### The unnormalised composition law -/

private lemma E2_mul (a a' b b' : ℂ) (m : ℕ) : ∀ n : ℕ,
    AHS (fun k => (k.factorial : ℂ) * E2 a a' m k * E2 b b' k n)
      (Complex.exp (a' * b) * E2 (a + b) (a' + b') m n) := by
  induction m with
  | zero =>
    intro n
    have h := E2_genfun b b' a' n
    have hfun : (fun k => (k.factorial : ℂ) * E2 a a' 0 k * E2 b b' k n) =
        fun k => a' ^ k * E2 b b' k n := by
      funext k
      have f1 : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [E2_zero_left]
      field_simp
    rw [hfun, E2_zero_left]
    have hval : Complex.exp (a' * b) * ((a' + b') ^ n / (n.factorial : ℂ)) =
        Complex.exp (b * a') * (a' + b') ^ n / (n.factorial : ℂ) := by
      rw [mul_comm b a']
      ring
    rw [hval]
    exact h
  | succ m ih =>
    intro n
    have hm : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    have rA := E2_row_zero a a' m
    cases n with
    | zero =>
      have hstep := AHS_add (AHS_const_mul b (ih 0)) (AHS_const_mul a (AHS_shift (ih 0)))
      refine AHS_step (c := (m : ℂ) + 1) hm hstep (fun k => ?_) ?_
      · have r1 := E2_row_succ a a' m k
        have r2 := E2_row_zero b b' k
        show ((m : ℂ) + 1) * (((k + 1).factorial : ℂ) * E2 a a' (m + 1) (k + 1) *
            E2 b b' (k + 1) 0) =
          b * ((k.factorial : ℂ) * E2 a a' m k * E2 b b' k 0) +
            a * (((k + 1).factorial : ℂ) * E2 a a' m (k + 1) * E2 b b' (k + 1) 0)
        rw [Nat.factorial_succ]
        push_cast
        linear_combination ((k : ℂ) + 1) * (k.factorial : ℂ) * E2 b b' (k + 1) 0 * r1 +
          (k.factorial : ℂ) * E2 a a' m k * r2
      · have rP := E2_row_zero (a + b) (a' + b') m
        show ((m : ℂ) + 1) * (((0 : ℕ).factorial : ℂ) * E2 a a' (m + 1) 0 * E2 b b' 0 0) +
            (b * (Complex.exp (a' * b) * E2 (a + b) (a' + b') m 0) +
              a * (Complex.exp (a' * b) * E2 (a + b) (a' + b') m 0 -
                ((0 : ℕ).factorial : ℂ) * E2 a a' m 0 * E2 b b' 0 0)) =
          ((m : ℂ) + 1) * (Complex.exp (a' * b) * E2 (a + b) (a' + b') (m + 1) 0)
        linear_combination ((0 : ℕ).factorial : ℂ) * E2 b b' 0 0 * rA -
          Complex.exp (a' * b) * rP
    | succ n =>
      have hstep := AHS_add (AHS_add (ih n) (AHS_const_mul b (ih (n + 1))))
        (AHS_const_mul a (AHS_shift (ih (n + 1))))
      refine AHS_step (c := (m : ℂ) + 1) hm hstep (fun k => ?_) ?_
      · have r1 := E2_row_succ a a' m k
        have r2 := E2_row_succ b b' k n
        show ((m : ℂ) + 1) * (((k + 1).factorial : ℂ) * E2 a a' (m + 1) (k + 1) *
            E2 b b' (k + 1) (n + 1)) =
          (k.factorial : ℂ) * E2 a a' m k * E2 b b' k n +
            b * ((k.factorial : ℂ) * E2 a a' m k * E2 b b' k (n + 1)) +
            a * (((k + 1).factorial : ℂ) * E2 a a' m (k + 1) * E2 b b' (k + 1) (n + 1))
        rw [Nat.factorial_succ]
        push_cast
        linear_combination ((k : ℂ) + 1) * (k.factorial : ℂ) * E2 b b' (k + 1) (n + 1) * r1 +
          (k.factorial : ℂ) * E2 a a' m k * r2
      · have rP := E2_row_succ (a + b) (a' + b') m n
        show ((m : ℂ) + 1) * (((0 : ℕ).factorial : ℂ) * E2 a a' (m + 1) 0 * E2 b b' 0 (n + 1)) +
            (Complex.exp (a' * b) * E2 (a + b) (a' + b') m n +
              b * (Complex.exp (a' * b) * E2 (a + b) (a' + b') m (n + 1)) +
              a * (Complex.exp (a' * b) * E2 (a + b) (a' + b') m (n + 1) -
                ((0 : ℕ).factorial : ℂ) * E2 a a' m 0 * E2 b b' 0 (n + 1))) =
          ((m : ℂ) + 1) * (Complex.exp (a' * b) * E2 (a + b) (a' + b') (m + 1) (n + 1))
        linear_combination ((0 : ℕ).factorial : ℂ) * E2 b b' 0 (n + 1) * rA -
          Complex.exp (a' * b) * rP

/-! ### Back to the normalised matrix -/

private lemma disp_eq (z : ℂ) (m n : ℕ) :
    displacementMatrix z m n =
      ((Real.exp (-Complex.normSq z / 2) *
        Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) : ℝ) : ℂ) *
        E2 z (-star z) m n := rfl

private lemma disp_mul_eq (a b : ℂ) (m n k : ℕ) :
    displacementMatrix a m k * displacementMatrix b k n =
      ((Real.exp (-Complex.normSq a / 2) : ℝ) : ℂ) * ((Real.exp (-Complex.normSq b / 2) : ℝ) : ℂ) *
        ((Real.sqrt (m.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n.factorial : ℝ) : ℝ) : ℂ) *
        ((k.factorial : ℂ) * E2 a (-star a) m k * E2 b (-star b) k n) := by
  rw [disp_eq, disp_eq]
  have hk : ((Real.sqrt (k.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (k.factorial : ℝ) : ℝ) : ℂ) =
      (k.factorial : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _), ← hk]
  simp only [Complex.ofReal_mul]
  ring

private lemma exp_const (a b : ℂ) :
    Complex.exp ((a * star b - star a * b) / 2) *
        ((Real.exp (-Complex.normSq (a + b) / 2) : ℝ) : ℂ) =
      ((Real.exp (-Complex.normSq a / 2) : ℝ) : ℂ) * ((Real.exp (-Complex.normSq b / 2) : ℝ) : ℂ) *
        Complex.exp (-star a * b) := by
  rw [Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj, ← Complex.mul_conj]
  simp only [Complex.star_def, map_add]
  ring

theorem solution (a b : ℂ) (m n : ℕ) :
    Summable (fun k : ℕ => ‖displacementMatrix a m k‖ * ‖displacementMatrix b k n‖) ∧
    HasSum (fun k : ℕ => displacementMatrix a m k * displacementMatrix b k n)
      (Complex.exp ((a * star b - star a * b) / 2) * displacementMatrix (a + b) m n) := by
  have h := AHS_const_mul
    (((Real.exp (-Complex.normSq a / 2) : ℝ) : ℂ) * ((Real.exp (-Complex.normSq b / 2) : ℝ) : ℂ) *
      ((Real.sqrt (m.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n.factorial : ℝ) : ℝ) : ℂ))
    (E2_mul a (-star a) b (-star b) m n)
  have hfun : (fun k : ℕ => displacementMatrix a m k * displacementMatrix b k n) = _ :=
    funext (disp_mul_eq a b m n)
  refine ⟨?_, ?_⟩
  · have h1 : (fun k : ℕ => ‖displacementMatrix a m k‖ * ‖displacementMatrix b k n‖) =
        fun k : ℕ => ‖displacementMatrix a m k * displacementMatrix b k n‖ := by
      funext k
      rw [norm_mul]
    rw [h1]
    simp only [disp_mul_eq]
    exact h.1
  · rw [hfun]
    have hval : Complex.exp ((a * star b - star a * b) / 2) * displacementMatrix (a + b) m n =
        ((Real.exp (-Complex.normSq a / 2) : ℝ) : ℂ) *
          ((Real.exp (-Complex.normSq b / 2) : ℝ) : ℂ) *
          ((Real.sqrt (m.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n.factorial : ℝ) : ℝ) : ℂ) *
          (Complex.exp (-star a * b) * E2 (a + b) (-star a + -star b) m n) := by
      have hs : -star a + -star b = -star (a + b) := by rw [star_add, neg_add]
      rw [hs, disp_eq, Real.sqrt_mul (Nat.cast_nonneg _)]
      simp only [Complex.ofReal_mul]
      linear_combination ((Real.sqrt (m.factorial : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt (n.factorial : ℝ) : ℝ) : ℂ) * E2 (a + b) (-star (a + b)) m n * exp_const a b
    rw [hval]
    exact h.2
