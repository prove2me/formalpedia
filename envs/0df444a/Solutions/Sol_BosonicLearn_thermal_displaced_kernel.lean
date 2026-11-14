-- Prove2me | solution 1 for BosonicLearn.thermal_displaced_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:32:12.504232+00:00
-- url     : https://prove2.me/submissions/c57f3367-a5b7-49af-80a8-47ec9b70ebb8

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


/-! ### Conjugation and scaling of `E2` -/

private lemma E2_star (x y : ℂ) (m n : ℕ) : star (E2 x y m n) = E2 (star x) (star y) m n := by
  unfold E2
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, map_div₀, map_mul, map_pow, map_natCast]

private lemma E2_scale (s : ℂ) (hs : s ≠ 0) (x y : ℂ) (m k : ℕ) :
    s ^ m * E2 x y m k = s ^ k * E2 (s * x) (y / s) m k := by
  unfold E2
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ min m k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨a, rfl⟩ : ∃ a, m = j + a := ⟨m - j, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = j + b := ⟨k - j, by omega⟩
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, mul_pow, div_pow, pow_add, pow_add]
  field_simp

/-! ### Double series -/

private lemma AHS_prod {f : ℕ × ℕ → ℂ} {R : ℕ → ℂ} {N : ℕ → ℝ} {S : ℂ}
    (hrow : ∀ u, HasSum (fun v => f (u, v)) (R u))
    (hrowN : ∀ u, HasSum (fun v => ‖f (u, v)‖) (N u))
    (hN : Summable N) (hR : HasSum R S) :
    Summable (fun x => ‖f x‖) ∧ HasSum f S := by
  have hn : Summable (fun x : ℕ × ℕ => ‖f x‖) := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun u => (hrowN u).summable, ?_⟩
    have : (fun u => ∑' v, ‖f (u, v)‖) = N := funext fun u => (hrowN u).tsum_eq
    rw [this]
    exact hN
  refine ⟨hn, ?_⟩
  have hs : Summable f := hn.of_norm
  have h2 := hs.hasSum.prod_fiberwise hrow
  rw [← h2.unique hR]
  exact hs.hasSum

private lemma hasSum_antidiagonal {α : Type} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T3Space α] {g : ℕ × ℕ → α} {S : α} (hs : HasSum g S) :
    HasSum (fun u => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal u, g p) S := by
  have h1 : HasSum (g ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) S :=
    (Equiv.hasSum_iff Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).mpr hs
  refine h1.sigma fun u => ?_
  have h2 := hasSum_fintype (fun c : Finset.HasAntidiagonal.antidiagonal u => g c)
  rw [Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal u) g] at h2
  exact h2

private lemma AHS_antidiagonal {g : ℕ × ℕ → ℂ} {S : ℂ} (hn : Summable fun p => ‖g p‖)
    (hs : HasSum g S) : AHS (fun u => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal u, g p) S := by
  refine ⟨?_, hasSum_antidiagonal hs⟩
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun u => norm_sum_le _ _)
    (hasSum_antidiagonal hn.hasSum).summable

/-! ### The diagonal generating function (Laguerre) -/

private lemma exp_AHS (x : ℂ) :
    AHS (fun m : ℕ => x ^ m / (m.factorial : ℂ)) (Complex.exp x) := by
  refine ⟨NormedSpace.norm_expSeries_div_summable x, ?_⟩
  have := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Complex.exp_eq_exp_ℂ] at this
  simpa using this

private lemma laguerre_term (r t : ℂ) (X Y : ℂ) (ht : t = X * Y) (k d : ℕ) :
    (((d + k).choose k : ℕ) : ℂ) * r ^ d * ((r * t) ^ k / (k.factorial : ℂ)) =
      r ^ (k + d) * ((k + d).factorial : ℂ) *
        (X ^ k * Y ^ k / ((d.factorial : ℂ) * (k.factorial : ℂ) * (k.factorial : ℂ))) := by
  have hf : (((d + k).choose k : ℕ) : ℂ) * (d.factorial : ℂ) * (k.factorial : ℂ) =
      ((k + d).factorial : ℂ) := by
    rw [add_comm k d]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial d k
  have f1 : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [← hf, ht]
  field_simp
  ring


private def lagG (r t : ℂ) (p : ℕ × ℕ) : ℂ :=
  (((p.2 + p.1).choose p.1 : ℕ) : ℂ) * r ^ p.2 * ((r * t) ^ p.1 / (p.1.factorial : ℂ))

private lemma lagG_row (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℂ) (m : ℕ) :
    HasSum (fun j => lagG r t (m, j))
      (1 / (1 - (r : ℂ)) ^ (m + 1) * (((r : ℂ) * t) ^ m / (m.factorial : ℂ))) := by
  have hrC : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg hr0]
    exact hr1
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) m hrC).mul_right
    (((r : ℂ) * t) ^ m / (m.factorial : ℂ))
  exact h

private lemma lagG_rowN (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℂ) (m : ℕ) :
    HasSum (fun j => ‖lagG r t (m, j)‖)
      (‖1 / (1 - (r : ℂ)) ^ (m + 1) * (((r : ℂ) * t) ^ m / (m.factorial : ℂ))‖) := by
  have hrR : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg hr0]
    exact hr1
  have hnr : ‖(1 - (r : ℂ))‖ = 1 - r := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) m hrR).mul_right
    ‖((r : ℂ) * t) ^ m / (m.factorial : ℂ)‖
  have e1 : (fun j => ‖lagG r t (m, j)‖) = fun j : ℕ =>
      (((j + m).choose m : ℕ) : ℝ) * r ^ j * ‖((r : ℂ) * t) ^ m / (m.factorial : ℂ)‖ := by
    funext j
    show ‖(((j + m).choose m : ℕ) : ℂ) * (r : ℂ) ^ j *
      (((r : ℂ) * t) ^ m / (m.factorial : ℂ))‖ = _
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_of_nonneg hr0]
  have e2 : ‖1 / (1 - (r : ℂ)) ^ (m + 1) * (((r : ℂ) * t) ^ m / (m.factorial : ℂ))‖ =
      1 / (1 - r) ^ (m + 1) * ‖((r : ℂ) * t) ^ m / (m.factorial : ℂ)‖ := by
    rw [norm_mul, norm_div, norm_one, norm_pow, hnr]
  rw [e1, e2]
  exact h

private lemma laguerre_AHS (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (X Y : ℂ) :
    AHS (fun u : ℕ => (r : ℂ) ^ u * (u.factorial : ℂ) * E2 X Y u u)
      ((1 - (r : ℂ))⁻¹ * Complex.exp (r * (X * Y) / (1 - r))) := by
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = X * Y := ⟨_, rfl⟩
  rw [← ht]
  have h1r : (1 - (r : ℂ)) ≠ 0 := by
    have : (1 - r : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hexp := AHS_const_mul (1 - (r : ℂ))⁻¹ (exp_AHS ((r : ℂ) * t / (1 - r)))
  have hRfun : (fun m : ℕ => 1 / (1 - (r : ℂ)) ^ (m + 1) *
      (((r : ℂ) * t) ^ m / (m.factorial : ℂ))) =
      fun m : ℕ => (1 - (r : ℂ))⁻¹ * (((r : ℂ) * t / (1 - r)) ^ m / (m.factorial : ℂ)) := by
    funext m
    rw [div_pow, pow_succ]
    field_simp
  have hN : Summable (fun m : ℕ => ‖1 / (1 - (r : ℂ)) ^ (m + 1) *
      (((r : ℂ) * t) ^ m / (m.factorial : ℂ))‖) := by
    have := hexp.1
    rw [← hRfun] at this
    exact this
  have hR : HasSum (fun m : ℕ => 1 / (1 - (r : ℂ)) ^ (m + 1) *
      (((r : ℂ) * t) ^ m / (m.factorial : ℂ)))
      ((1 - (r : ℂ))⁻¹ * Complex.exp (r * t / (1 - r))) := by
    rw [hRfun]
    exact hexp.2
  obtain ⟨hgn, hgs⟩ := AHS_prod (f := lagG r t) (lagG_row r hr0 hr1 t) (lagG_rowN r hr0 hr1 t)
    hN hR
  have hfin := AHS_antidiagonal hgn hgs
  have hfun : (fun u : ℕ => (r : ℂ) ^ u * (u.factorial : ℂ) * E2 X Y u u) =
      fun u => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal u, lagG r t p := by
    funext u
    symm
    calc ∑ p ∈ Finset.HasAntidiagonal.antidiagonal u, lagG r t p
        = ∑ k ∈ Finset.range (u + 1), lagG r t (k, u - k) :=
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (lagG r t) u
      _ = ∑ k ∈ Finset.range (u + 1), (r : ℂ) ^ u * (u.factorial : ℂ) *
            (X ^ (u - (u + 1 - 1 - k)) * Y ^ (u - (u + 1 - 1 - k)) /
              (((u + 1 - 1 - k).factorial : ℂ) * ((u - (u + 1 - 1 - k)).factorial : ℂ) *
                ((u - (u + 1 - 1 - k)).factorial : ℂ))) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          obtain ⟨d, rfl⟩ : ∃ d, u = k + d := ⟨u - k, by omega⟩
          have e1 : k + d + 1 - 1 - k = d := by omega
          have e2 : k + d - d = k := by omega
          have e3 : k + d - k = d := by omega
          rw [e1, e2, e3]
          exact laguerre_term (r : ℂ) t X Y ht k d
      _ = (r : ℂ) ^ u * (u.factorial : ℂ) * ∑ k ∈ Finset.range (u + 1),
            (X ^ (u - (u + 1 - 1 - k)) * Y ^ (u - (u + 1 - 1 - k)) /
              (((u + 1 - 1 - k).factorial : ℂ) * ((u - (u + 1 - 1 - k)).factorial : ℂ) *
                ((u - (u + 1 - 1 - k)).factorial : ℂ))) := by
          rw [Finset.mul_sum]
      _ = (r : ℂ) ^ u * (u.factorial : ℂ) * E2 X Y u u := by
          rw [Finset.sum_range_reflect (fun j => X ^ (u - j) * Y ^ (u - j) /
              ((j.factorial : ℂ) * ((u - j).factorial : ℂ) * ((u - j).factorial : ℂ))) (u + 1)]
          unfold E2
          rw [min_self]
  rw [hfun]
  exact hfin

/-! ### One mode: the displaced thermal state -/

/-- `κ = (1 - r)/√r`. -/
private def kap (r : ℝ) : ℂ := (((1 - r) / Real.sqrt r : ℝ) : ℂ)

/-- One-mode thermal weights. -/
private def qw (r : ℝ) (w : ℕ) : ℝ := (1 - r) * r ^ w

/-- Closed form of the one-mode displaced thermal state `τ_y = D(y) τ D(y)†`. -/
private def tauC (r : ℝ) (y : ℂ) (u v : ℕ) : ℂ :=
  (((1 - r) * Real.exp (-(1 - r) * Complex.normSq y) * Real.sqrt (u.factorial : ℝ) *
      Real.sqrt (v.factorial : ℝ) * Real.sqrt r ^ (u + v) : ℝ) : ℂ) *
    E2 (kap r * y) (kap r * star y) u v

private lemma sqrt_fact_mul_self (w : ℕ) :
    ((Real.sqrt (w.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (w.factorial : ℝ) : ℝ) : ℂ) =
      (w.factorial : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

private lemma tau_term (r : ℝ) (hr0 : 0 < r) (y : ℂ) (u v w : ℕ) :
    displacementMatrix y u w * ((qw r w : ℝ) : ℂ) * star (displacementMatrix y v w) =
      ((Real.exp (-Complex.normSq y) : ℝ) : ℂ) * ((Real.sqrt (u.factorial : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt (v.factorial : ℝ) : ℝ) : ℂ) * ((1 - r : ℝ) : ℂ) *
        ((Real.sqrt r : ℝ) : ℂ) ^ u * ((Real.sqrt r : ℝ) : ℂ) ^ v *
        ((w.factorial : ℂ) * E2 (y / ((Real.sqrt r : ℝ) : ℂ)) (-star y * ((Real.sqrt r : ℝ) : ℂ)) u w *
          E2 (((Real.sqrt r : ℝ) : ℂ) * -y) (star y / ((Real.sqrt r : ℝ) : ℂ)) w v) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt r := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.mpr hr0
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hss : (r : ℂ) = (s : ℂ) * s := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hr0.le]
  have he : ((Real.exp (-Complex.normSq y / 2) : ℝ) : ℂ) * ((Real.exp (-Complex.normSq y / 2) : ℝ) : ℂ) =
      ((Real.exp (-Complex.normSq y) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have h1 : (s : ℂ) ^ w * E2 y (-star y) u w =
      (s : ℂ) ^ u * E2 (y / s) (-star y * s) u w := by
    have := E2_scale (s : ℂ) hsC (y / s) (-star y * s) u w
    rw [mul_div_cancel₀ _ hsC, mul_div_cancel_right₀ _ hsC] at this
    exact this.symm
  have h2 : (s : ℂ) ^ w * E2 (-y) (star y) w v =
      (s : ℂ) ^ v * E2 ((s : ℂ) * -y) (star y / s) w v := E2_scale (s : ℂ) hsC (-y) (star y) w v
  have hst : star (displacementMatrix y v w) =
      ((Real.exp (-Complex.normSq y / 2) *
        Real.sqrt ((Nat.factorial v : ℝ) * (Nat.factorial w : ℝ)) : ℝ) : ℂ) *
        E2 (-y) (star y) w v := by
    rw [disp_eq, star_mul', E2_star, star_neg, star_star, E2_symm, Complex.star_def,
      Complex.conj_ofReal]
  rw [hst, disp_eq, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _)]
  unfold qw
  calc _ = (((Real.exp (-Complex.normSq y / 2) : ℝ) : ℂ) * ((Real.exp (-Complex.normSq y / 2) : ℝ) : ℂ)) *
        ((Real.sqrt (u.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (v.factorial : ℝ) : ℝ) : ℂ) *
        ((1 - r : ℝ) : ℂ) *
        (((Real.sqrt (w.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (w.factorial : ℝ) : ℝ) : ℂ)) *
        (((s : ℂ) ^ w * E2 y (-star y) u w) * ((s : ℂ) ^ w * E2 (-y) (star y) w v)) := by
        push_cast
        rw [hss, mul_pow]
        ring
    _ = _ := by
        rw [h1, h2, he, sqrt_fact_mul_self]
        ring

private lemma kap_eq (r : ℝ) (hr0 : 0 < r) :
    kap r * ((Real.sqrt r : ℝ) : ℂ) = 1 - (r : ℂ) := by
  have hsC : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr0).ne'
  unfold kap
  push_cast
  field_simp

private lemma sqrt_mul_self_C (r : ℝ) (hr0 : 0 < r) :
    ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0.le]

private lemma tau_AHS (r : ℝ) (hr0 : 0 < r) (y : ℂ) (u v : ℕ) :
    AHS (fun w => displacementMatrix y u w * ((qw r w : ℝ) : ℂ) *
        star (displacementMatrix y v w)) (tauC r y u v) := by
  have hsC : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr0).ne'
  have hk := kap_eq r hr0
  have hss := sqrt_mul_self_C r hr0
  have h := AHS_const_mul
    (((Real.exp (-Complex.normSq y) : ℝ) : ℂ) * ((Real.sqrt (u.factorial : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt (v.factorial : ℝ) : ℝ) : ℂ) * ((1 - r : ℝ) : ℂ) *
        ((Real.sqrt r : ℝ) : ℂ) ^ u * ((Real.sqrt r : ℝ) : ℂ) ^ v)
    (E2_mul (y / ((Real.sqrt r : ℝ) : ℂ)) (-star y * ((Real.sqrt r : ℝ) : ℂ))
      (((Real.sqrt r : ℝ) : ℂ) * -y) (star y / ((Real.sqrt r : ℝ) : ℂ)) u v)
  have hfun : (fun w => displacementMatrix y u w * ((qw r w : ℝ) : ℂ) *
      star (displacementMatrix y v w)) = _ := funext (tau_term r hr0 y u v)
  rw [hfun]
  have ha : y / ((Real.sqrt r : ℝ) : ℂ) + ((Real.sqrt r : ℝ) : ℂ) * -y = kap r * y := by
    field_simp
    linear_combination -y * hss - y * hk
  have hb : -star y * ((Real.sqrt r : ℝ) : ℂ) + star y / ((Real.sqrt r : ℝ) : ℂ) =
      kap r * star y := by
    field_simp
    linear_combination -star y * hss - star y * hk
  have hexp : Complex.exp (-(1 - (r : ℂ)) * (Complex.normSq y : ℂ)) =
      Complex.exp (-(Complex.normSq y : ℂ)) *
        Complex.exp (-star y * ((Real.sqrt r : ℝ) : ℂ) * (((Real.sqrt r : ℝ) : ℂ) * -y)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [← Complex.mul_conj y, ← Complex.star_def]
    linear_combination -(y * star y) * hss
  have hval : ((Real.exp (-Complex.normSq y) : ℝ) : ℂ) * ((Real.sqrt (u.factorial : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt (v.factorial : ℝ) : ℝ) : ℂ) * ((1 - r : ℝ) : ℂ) *
        ((Real.sqrt r : ℝ) : ℂ) ^ u * ((Real.sqrt r : ℝ) : ℂ) ^ v *
      (Complex.exp (-star y * ((Real.sqrt r : ℝ) : ℂ) * (((Real.sqrt r : ℝ) : ℂ) * -y)) *
        E2 (kap r * y) (kap r * star y) u v) = tauC r y u v := by
    unfold tauC
    push_cast
    rw [hexp, pow_add]
    ring
  rw [ha, hb, hval] at h
  exact h

/-! ### One mode: the kernel -/

/-- The one-mode kernel summand `(τ_z)_{uv} conj((τ_{z'})_{uv}) / √(q_u q_v)`. -/
private def Kc (r : ℝ) (z z' : ℂ) (u v : ℕ) : ℂ :=
  tauC r z u v * star (tauC r z' u v) / ((Real.sqrt (qw r u * qw r v) : ℝ) : ℂ)

private lemma sqrt_qw (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (u v : ℕ) :
    Real.sqrt (qw r u * qw r v) = (1 - r) * Real.sqrt r ^ (u + v) := by
  have h : qw r u * qw r v = ((1 - r) * Real.sqrt r ^ (u + v)) ^ 2 := by
    unfold qw
    have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
    calc (1 - r) * r ^ u * ((1 - r) * r ^ v) = (1 - r) ^ 2 * r ^ (u + v) := by ring
      _ = (1 - r) ^ 2 * (Real.sqrt r ^ 2) ^ (u + v) := by rw [hs]
      _ = _ := by ring
  have h1 : 0 ≤ 1 - r := by linarith
  rw [h, Real.sqrt_sq (mul_nonneg h1 (pow_nonneg (Real.sqrt_nonneg r) _))]

private lemma kap_star (r : ℝ) : star (kap r) = kap r := by
  unfold kap
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The row sums of the one-mode kernel. -/
private def Rc (r : ℝ) (z z' : ℂ) (u : ℕ) : ℂ :=
  ((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
      ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) *
      Complex.exp (kap r * star z * (((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))) *
    ((r : ℂ) ^ u * (u.factorial : ℂ) *
      E2 (kap r * z + ((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))
        (kap r * star z + kap r * star z' / ((Real.sqrt r : ℝ) : ℂ)) u u)

private lemma kern_term (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z z' : ℂ) (u v : ℕ) :
    Kc r z z' u v =
      ((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
        ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) * (u.factorial : ℂ) *
        ((Real.sqrt r : ℝ) : ℂ) ^ u * ((Real.sqrt r : ℝ) : ℂ) ^ u *
      ((v.factorial : ℂ) * E2 (kap r * z) (kap r * star z) u v *
        E2 (((Real.sqrt r : ℝ) : ℂ) * (kap r * z')) (kap r * star z' / ((Real.sqrt r : ℝ) : ℂ))
          v u) := by
  have hsC : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr0).ne'
  have h1r : ((1 - r : ℝ) : ℂ) ≠ 0 := by
    have : (1 - r : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have h2 : ((Real.sqrt r : ℝ) : ℂ) ^ v * E2 (kap r * z') (kap r * star z') v u =
      ((Real.sqrt r : ℝ) : ℂ) ^ u * E2 (((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))
        (kap r * star z' / ((Real.sqrt r : ℝ) : ℂ)) v u :=
    E2_scale _ hsC _ _ v u
  have hst : star (tauC r z' u v) =
      (((1 - r) * Real.exp (-(1 - r) * Complex.normSq z') * Real.sqrt (u.factorial : ℝ) *
        Real.sqrt (v.factorial : ℝ) * Real.sqrt r ^ (u + v) : ℝ) : ℂ) *
      E2 (kap r * z') (kap r * star z') v u := by
    unfold tauC
    rw [star_mul', E2_star, star_mul', star_mul', star_star, kap_star, E2_symm, Complex.star_def,
      Complex.conj_ofReal]
  rw [Kc, hst, sqrt_qw r hr0 hr1, tauC]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  calc _ = ((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
        ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) ^ u *
        (((Real.sqrt (u.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (u.factorial : ℝ) : ℝ) : ℂ)) *
        (((Real.sqrt (v.factorial : ℝ) : ℝ) : ℂ) * ((Real.sqrt (v.factorial : ℝ) : ℝ) : ℂ)) *
        (E2 (kap r * z) (kap r * star z) u v *
          (((Real.sqrt r : ℝ) : ℂ) ^ v * E2 (kap r * z') (kap r * star z') v u)) := by
        rw [pow_add]
        field_simp
    _ = _ := by
        rw [h2, sqrt_fact_mul_self, sqrt_fact_mul_self]
        ring

private lemma kern_row (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z z' : ℂ) (u : ℕ) :
    AHS (fun v => Kc r z z' u v) (Rc r z z' u) := by
  have h := AHS_const_mul
    (((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
        ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) * (u.factorial : ℂ) *
        ((Real.sqrt r : ℝ) : ℂ) ^ u * ((Real.sqrt r : ℝ) : ℂ) ^ u)
    (E2_mul (kap r * z) (kap r * star z) (((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))
      (kap r * star z' / ((Real.sqrt r : ℝ) : ℂ)) u u)
  have hfun : (fun v => Kc r z z' u v) = _ := funext (kern_term r hr0 hr1 z z' u)
  rw [hfun]
  have hval : ((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
        ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) * (u.factorial : ℂ) *
        ((Real.sqrt r : ℝ) : ℂ) ^ u * ((Real.sqrt r : ℝ) : ℂ) ^ u *
      (Complex.exp (kap r * star z * (((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))) *
        E2 (kap r * z + ((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))
          (kap r * star z + kap r * star z' / ((Real.sqrt r : ℝ) : ℂ)) u u) = Rc r z z' u := by
    unfold Rc
    rw [← sqrt_mul_self_C r hr0, mul_pow]
    ring
  rw [hval] at h
  exact h

private lemma exponent_identity (s z z' w w' : ℂ) (hs : s ≠ 0) (_h1 : 1 - s * s ≠ 0) :
    -(1 - s * s) * (z * w) + -(1 - s * s) * (z' * w') +
        (1 - s * s) / s * w * (s * ((1 - s * s) / s * z')) +
      s * s * (((1 - s * s) / s * z + s * ((1 - s * s) / s * z')) *
        ((1 - s * s) / s * w + (1 - s * s) / s * w' / s)) / (1 - s * s) =
    (1 - s * s) / s * (w * z' + z * w') := by
  field_simp
  ring

private lemma kern_total (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z z' : ℂ) :
    AHS (Rc r z z') (Complex.exp (kap r * (star z * z' + z * star z'))) := by
  have hsC : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr0).ne'
  have hss := sqrt_mul_self_C r hr0
  have h1r : (1 - (r : ℂ)) ≠ 0 := by
    have : (1 - r : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hkap : kap r = (1 - ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ)) /
      ((Real.sqrt r : ℝ) : ℂ) := by
    rw [hss]
    unfold kap
    push_cast
    rfl
  have h := AHS_const_mul
    (((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
      ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) *
      Complex.exp (kap r * star z * (((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))))
    (laguerre_AHS r hr0.le hr1 (kap r * z + ((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))
        (kap r * star z + kap r * star z' / ((Real.sqrt r : ℝ) : ℂ)))
  have hval : ((1 - r : ℝ) : ℂ) * ((Real.exp (-(1 - r) * Complex.normSq z) : ℝ) : ℂ) *
      ((Real.exp (-(1 - r) * Complex.normSq z') : ℝ) : ℂ) *
      Complex.exp (kap r * star z * (((Real.sqrt r : ℝ) : ℂ) * (kap r * z'))) *
      ((1 - (r : ℂ))⁻¹ * Complex.exp ((r : ℂ) *
        ((kap r * z + ((Real.sqrt r : ℝ) : ℂ) * (kap r * z')) *
          (kap r * star z + kap r * star z' / ((Real.sqrt r : ℝ) : ℂ))) / (1 - r))) =
      Complex.exp (kap r * (star z * z' + z * star z')) := by
    have e0 : ((1 - r : ℝ) : ℂ) = 1 - (r : ℂ) := by push_cast; rfl
    rw [Complex.ofReal_exp, Complex.ofReal_exp, e0]
    have e1 : ∀ A B C D : ℂ, (1 - (r : ℂ)) * A * B * C * ((1 - (r : ℂ))⁻¹ * D) = A * B * C * D := by
      intro A B C D
      field_simp
    rw [e1, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    rw [← Complex.mul_conj z, ← Complex.mul_conj z', ← Complex.star_def, hkap, ← hss]
    exact exponent_identity _ z z' (star z) (star z') hsC (by rw [hss]; exact h1r)
  rw [hval] at h
  exact h

/-! ### One mode: absolute convergence of the double series -/

private lemma hasSum_norm_of_nonneg {f : ℕ → ℂ} {S : ℂ} (hpos : ∀ k, f k = ((‖f k‖ : ℝ) : ℂ))
    (hn : Summable fun k => ‖f k‖) (hs : HasSum f S) : HasSum (fun k => ‖f k‖) ‖S‖ := by
  have h1 : HasSum (fun k => ((‖f k‖ : ℝ) : ℂ)) ((∑' k, ‖f k‖ : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr hn.hasSum
  have h2 : HasSum f ((∑' k, ‖f k‖ : ℝ) : ℂ) := by
    have e : f = fun k => ((‖f k‖ : ℝ) : ℂ) := funext hpos
    rw [e]
    simpa using h1
  have h3 : S = ((∑' k, ‖f k‖ : ℝ) : ℂ) := hs.unique h2
  rw [h3, Complex.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  exact hn.hasSum

private lemma mul_star_div_ofReal (a : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    a * star a / (c : ℂ) = ((‖a * star a / (c : ℂ)‖ : ℝ) : ℂ) := by
  have h : a * star a / (c : ℂ) = ((Complex.normSq a / c : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_div]
  rw [h, Complex.norm_of_nonneg (div_nonneg (Complex.normSq_nonneg a) hc)]

private lemma amgm_norm (a b c : ℂ) :
    ‖a * star b / c‖ ≤ (‖a * star a / c‖ + ‖b * star b / c‖) / 2 := by
  simp only [norm_div, norm_mul, norm_star]
  have h : 0 ≤ (‖a‖ - ‖b‖) ^ 2 / ‖c‖ / 2 := by positivity
  have e : (‖a‖ * ‖a‖ / ‖c‖ + ‖b‖ * ‖b‖ / ‖c‖) / 2 - ‖a‖ * ‖b‖ / ‖c‖ =
      (‖a‖ - ‖b‖) ^ 2 / ‖c‖ / 2 := by ring
  linarith

private lemma kern_diag_summable (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) :
    Summable (fun x : ℕ × ℕ => ‖Kc r z z x.1 x.2‖) := by
  have htot := kern_total r hr0 hr1 z z
  refine (AHS_prod (f := fun x : ℕ × ℕ => Kc r z z x.1 x.2) (R := Rc r z z)
    (N := fun u => ‖Rc r z z u‖) (fun u => (kern_row r hr0 hr1 z z u).2) (fun u => ?_)
    htot.1 htot.2).1
  exact hasSum_norm_of_nonneg
    (fun v => mul_star_div_ofReal (tauC r z u v) _ (Real.sqrt_nonneg _))
    (kern_row r hr0 hr1 z z u).1 (kern_row r hr0 hr1 z z u).2

private lemma kern_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z z' : ℂ) :
    Summable (fun x : ℕ × ℕ => ‖Kc r z z' x.1 x.2‖) ∧
    HasSum (fun x : ℕ × ℕ => Kc r z z' x.1 x.2)
      (Complex.exp (kap r * (star z * z' + z * star z'))) := by
  have hn : Summable (fun x : ℕ × ℕ => ‖Kc r z z' x.1 x.2‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (((kern_diag_summable r hr0 hr1 z).add (kern_diag_summable r hr0 hr1 z')).div_const 2)
    exact amgm_norm _ _ _
  refine ⟨hn, ?_⟩
  have hs : Summable (fun x : ℕ × ℕ => Kc r z z' x.1 x.2) := hn.of_norm
  have h2 : HasSum (Rc r z z') (∑' x : ℕ × ℕ, Kc r z z' x.1 x.2) :=
    hs.hasSum.prod_fiberwise (fun u => (kern_row r hr0 hr1 z z' u).2)
  rw [← h2.unique (kern_total r hr0 hr1 z z').2]
  exact hs.hasSum

/-! ### Products of absolutely convergent series -/

/-- `PP ι α`: a product over the finite type `α` of absolutely convergent series over `ι` is an
absolutely convergent series over `α → ι`, with sum the product of the sums. -/
private def PP (ι : Type) (α : Type) [Fintype α] : Prop :=
  ∀ (f : α → ι → ℂ) (s : α → ℂ),
      (∀ i, Summable fun k => ‖f i k‖) → (∀ i, HasSum (f i) (s i)) →
      Summable (fun w : α → ι => ‖∏ i, f i (w i)‖) ∧
      HasSum (fun w : α → ι => ∏ i, f i (w i)) (∏ i, s i)

private lemma PP_equiv (ι : Type) (α β : Type) [Fintype α] [Fintype β] (e : α ≃ β)
    (ih : PP ι α) : PP ι β := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (e i)) (fun i => s (e i)) (fun i => hn (e i))
    (fun i => hs (e i))
  let E : (β → ι) ≃ (α → ι) := Equiv.arrowCongr e.symm (Equiv.refl ι)
  have hE : ∀ w : β → ι, ∏ i, f (e i) (E w i) = ∏ j, f j (w j) := by
    intro w
    exact Equiv.prod_comp e (fun j => f j (w j))
  have hsE : ∏ i, s (e i) = ∏ j, s j := Equiv.prod_comp e s
  refine ⟨?_, ?_⟩
  · have := (Equiv.summable_iff E).mpr h1
    have hfun : ((fun w : α → ι => ‖∏ i, f (e i) (w i)‖) ∘ E) =
        fun w : β → ι => ‖∏ j, f j (w j)‖ := by
      funext w
      show ‖∏ i, f (e i) (E w i)‖ = _
      rw [hE]
    rw [hfun] at this
    exact this
  · have := (Equiv.hasSum_iff E).mpr h2
    have hfun : ((fun w : α → ι => ∏ i, f (e i) (w i)) ∘ E) =
        fun w : β → ι => ∏ j, f j (w j) := by
      funext w
      show ∏ i, f (e i) (E w i) = _
      rw [hE]
    rw [hfun, hsE] at this
    exact this

private lemma PP_empty (ι : Type) : PP ι PEmpty := by
  intro f s _ _
  have h := hasSum_unique (fun w : PEmpty → ι => ∏ i, f i (w i))
  have hn := hasSum_unique (fun w : PEmpty → ι => ‖∏ i, f i (w i)‖)
  refine ⟨hn.summable, ?_⟩
  convert h using 1
  simp

private lemma PP_option (ι : Type) (α : Type) [Fintype α] (ih : PP ι α) : PP ι (Option α) := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (some i)) (fun i => s (some i)) (fun i => hn (some i))
    (fun i => hs (some i))
  let E : (Option α → ι) ≃ ι × (α → ι) := Equiv.piOptionEquivProd (β := fun _ => ι)
  have hmulN : Summable fun x : ι × (α → ι) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖ :=
    Summable.mul_norm (f := f none) (g := fun w : α → ι => ∏ i, f (some i) (w i)) (hn none) h1
  have hmulS : Summable fun x : ι × (α → ι) => f none x.1 * ∏ i, f (some i) (x.2 i) :=
    hmulN.of_norm
  have hmul : HasSum (fun x : ι × (α → ι) => f none x.1 * ∏ i, f (some i) (x.2 i))
      (s none * ∏ i, s (some i)) :=
    HasSum.mul (f := f none) (g := fun w : α → ι => ∏ i, f (some i) (w i)) (hs none) h2 hmulS
  have hEw : ∀ w : Option α → ι, E w = (w none, fun i => w (some i)) := fun w => rfl
  refine ⟨?_, ?_⟩
  · have h3 := (Equiv.summable_iff E).mpr hmulN
    have hfun : ((fun x : ι × (α → ι) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖) ∘ E) =
        fun w : Option α → ι => ‖∏ j, f j (w j)‖ := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun] at h3
    exact h3
  · have h3 := (Equiv.hasSum_iff E).mpr hmul
    have hfun : ((fun x : ι × (α → ι) => f none x.1 * ∏ i, f (some i) (x.2 i)) ∘ E) =
        fun w : Option α → ι => ∏ j, f j (w j) := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun, ← Fintype.prod_option s] at h3
    exact h3

private lemma hasSum_pi_prod (ι : Type) (I : Type) [Fintype I] : PP ι I := by
  refine Fintype.induction_empty_option (P := fun (α : Type) [Fintype α] => PP ι α) ?_ ?_ ?_ I
  · intro α β _ e ih
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    exact PP_equiv ι α β e ih
  · exact PP_empty ι
  · intro α _ ih
    exact PP_option ι α ih

/-! ### The `n`-mode statement -/

theorem solution {n : ℕ} (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z z' : Fin n → ℂ)
    (p : (Fin n → ℕ) → ℝ) (hp : p = fun w => (1 - r) ^ n * r ^ (∑ i, w i))
    (T : (Fin n → ℂ) → (Fin n → ℕ) → (Fin n → ℕ) → ℂ)
    (hT : T = fun z u v => ∑' w : Fin n → ℕ,
      (∏ j, displacementMatrix (z j) (u j) (w j)) * ((p w : ℝ) : ℂ) *
        star (∏ j, displacementMatrix (z j) (v j) (w j))) :
    (∀ (y : Fin n → ℂ) (u v : Fin n → ℕ), Summable fun w : Fin n → ℕ =>
      ‖(∏ j, displacementMatrix (y j) (u j) (w j)) * ((p w : ℝ) : ℂ) *
        star (∏ j, displacementMatrix (y j) (v j) (w j))‖) ∧
    Summable (fun x : (Fin n → ℕ) × (Fin n → ℕ) =>
      ‖T z x.1 x.2‖ * ‖T z' x.1 x.2‖ / Real.sqrt (p x.1 * p x.2)) ∧
    HasSum (fun x : (Fin n → ℕ) × (Fin n → ℕ) =>
      T z x.1 x.2 * star (T z' x.1 x.2) / ((Real.sqrt (p x.1 * p x.2) : ℝ) : ℂ))
      (Complex.exp ((((1 - r) / Real.sqrt r : ℝ) : ℂ) *
        ∑ j, (star (z j) * z' j + z j * star (z' j)))) := by
  have hpw : ∀ w : Fin n → ℕ, p w = ∏ j, qw r (w j) := by
    intro w
    rw [hp]
    unfold qw
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ,
      Fintype.card_fin]
  have hterm : ∀ (y : Fin n → ℂ) (u v w : Fin n → ℕ),
      (∏ j, displacementMatrix (y j) (u j) (w j)) * ((p w : ℝ) : ℂ) *
        star (∏ j, displacementMatrix (y j) (v j) (w j)) =
      ∏ j, (displacementMatrix (y j) (u j) (w j) * ((qw r (w j) : ℝ) : ℂ) *
        star (displacementMatrix (y j) (v j) (w j))) := by
    intro y u v w
    rw [hpw, Complex.ofReal_prod, star_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hP := fun (y : Fin n → ℂ) (u v : Fin n → ℕ) =>
    hasSum_pi_prod ℕ (Fin n)
      (fun j w => displacementMatrix (y j) (u j) w * ((qw r w : ℝ) : ℂ) *
        star (displacementMatrix (y j) (v j) w))
      (fun j => tauC r (y j) (u j) (v j))
      (fun j => (tau_AHS r hr0 (y j) (u j) (v j)).1)
      (fun j => (tau_AHS r hr0 (y j) (u j) (v j)).2)
  have hTval : ∀ (y : Fin n → ℂ) (u v : Fin n → ℕ),
      T y u v = ∏ j, tauC r (y j) (u j) (v j) := by
    intro y u v
    rw [hT]
    simp only [hterm]
    exact (hP y u v).2.tsum_eq
  have hsq : ∀ u v : Fin n → ℕ, ((Real.sqrt (p u * p v) : ℝ) : ℂ) =
      ∏ j, ((Real.sqrt (qw r (u j) * qw r (v j)) : ℝ) : ℂ) := by
    intro u v
    have hq : ∀ w : ℕ, 0 ≤ qw r w := fun w =>
      mul_nonneg (by linarith) (pow_nonneg hr0.le _)
    rw [hpw, hpw, ← Finset.prod_mul_distrib,
      Real.sqrt_prod _ (fun j _ => mul_nonneg (hq _) (hq _)), Complex.ofReal_prod]
  have hK : ∀ x : (Fin n → ℕ) × (Fin n → ℕ),
      T z x.1 x.2 * star (T z' x.1 x.2) / ((Real.sqrt (p x.1 * p x.2) : ℝ) : ℂ) =
        ∏ j, Kc r (z j) (z' j) (x.1 j) (x.2 j) := by
    intro x
    rw [hTval, hTval, hsq, star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    rfl
  have hKn : ∀ x : (Fin n → ℕ) × (Fin n → ℕ),
      ‖T z x.1 x.2‖ * ‖T z' x.1 x.2‖ / Real.sqrt (p x.1 * p x.2) =
        ‖∏ j, Kc r (z j) (z' j) (x.1 j) (x.2 j)‖ := by
    intro x
    rw [← hK, norm_div, norm_mul, norm_star, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  have key := hasSum_pi_prod (ℕ × ℕ) (Fin n) (fun j x => Kc r (z j) (z' j) x.1 x.2)
    (fun j => Complex.exp (kap r * (star (z j) * z' j + z j * star (z' j))))
    (fun j => (kern_one r hr0 hr1 (z j) (z' j)).1)
    (fun j => (kern_one r hr0 hr1 (z j) (z' j)).2)
  let E : ((Fin n → ℕ) × (Fin n → ℕ)) ≃ (Fin n → ℕ × ℕ) :=
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ℕ) (fun _ => ℕ)).symm
  refine ⟨?_, ?_, ?_⟩
  · intro y u v
    simp only [hterm]
    exact (hP y u v).1
  · have h3 := (Equiv.summable_iff E).mpr key.1
    have hfun : ((fun w : Fin n → ℕ × ℕ => ‖∏ j, Kc r (z j) (z' j) (w j).1 (w j).2‖) ∘ E) =
        fun x : (Fin n → ℕ) × (Fin n → ℕ) =>
          ‖T z x.1 x.2‖ * ‖T z' x.1 x.2‖ / Real.sqrt (p x.1 * p x.2) := by
      funext x
      rw [hKn]
      rfl
    rw [hfun] at h3
    exact h3
  · have h3 := (Equiv.hasSum_iff E).mpr key.2
    have hfun : ((fun w : Fin n → ℕ × ℕ => ∏ j, Kc r (z j) (z' j) (w j).1 (w j).2) ∘ E) =
        fun x : (Fin n → ℕ) × (Fin n → ℕ) =>
          T z x.1 x.2 * star (T z' x.1 x.2) / ((Real.sqrt (p x.1 * p x.2) : ℝ) : ℂ) := by
      funext x
      rw [hK]
      rfl
    have hval : ∏ j, Complex.exp (kap r * (star (z j) * z' j + z j * star (z' j))) =
        Complex.exp ((((1 - r) / Real.sqrt r : ℝ) : ℂ) *
          ∑ j, (star (z j) * z' j + z j * star (z' j))) := by
      rw [Finset.mul_sum, Complex.exp_sum]
      rfl
    rw [hfun, hval] at h3
    exact h3
