-- Prove2me | solution 1 for BosonicLearn.coherent_weyl_integral
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:17:10.970428+00:00
-- url     : https://prove2.me/submissions/bca227c7-c0d6-4f52-9d8b-aa8e44cc837a

import Mathlib
import Definitions.Def_BosonicLearn_coherentVector
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (oscillatorWeylKernel)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open MeasureTheory
open BosonicLearn

/-!
# `coherent_weyl_integral`

Route.  For `p = (x, y) : ℝ × ℝ` put `z = x + i y` and
`J m k a b = ∫ z^m z̄^k e^{-(x²+y²)/2 + a z + b z̄} dx dy`  (`a b : ℂ`).

* `J_zero_zero`: `J 0 0 a b = 2π e^{2ab}` (product of two one-dimensional complex Gaussians).
* `J_hasDerivAt_a`, `J_hasDerivAt_b`: differentiation under the integral sign,
  `∂_a J m k = J (m+1) k`, `∂_b J m k = J m (k+1)`.
* `J_zero_left`, `J_row`: hence `J 0 k = 2π e^{2ab} (2a)^k` and the ladder recursion
  `J (m+1) k = 2b J m k + 2k J m (k-1)`.
* `J_eq`: closed form, by the row recursion of the unnormalised displacement matrix `E2`.
* `modeFn_integral`: the single-mode identity; `solution`: product over the modes.
-/

noncomputable section

/-- `z = x + i y`. -/
private def zz (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + Complex.I * (p.2 : ℂ)

/-- `z̄ = x - i y`. -/
private def zb (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) - Complex.I * (p.2 : ℂ)

/-- The integrand `z^m z̄^k e^{-(x²+y²)/2 + a z + b z̄}`. -/
private def FJ (m k : ℕ) (a b : ℂ) (p : ℝ × ℝ) : ℂ :=
  zz p ^ m * zb p ^ k *
    Complex.exp (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + a * zz p + b * zb p)

private def J (m k : ℕ) (a b : ℂ) : ℂ := ∫ p : ℝ × ℝ, FJ m k a b p

private lemma zz_norm_sq (p : ℝ × ℝ) : ‖zz p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [zz]
  ring

private lemma zb_eq_conj (p : ℝ × ℝ) : zb p = (starRingEnd ℂ) (zz p) := by
  simp [zz, zb, sub_eq_add_neg]

private lemma zb_norm (p : ℝ × ℝ) : ‖zb p‖ = ‖zz p‖ := by
  rw [zb_eq_conj, RCLike.norm_conj]

private lemma real_bound (N : ℕ) (c r : ℝ) (hr : 0 ≤ r) :
    r ^ N * Real.exp (-(r ^ 2) / 2 + c * r) ≤
      Real.exp ((c + N) ^ 2) * Real.exp (-(r ^ 2) / 4) := by
  have h1 : r ^ N ≤ Real.exp (N * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hr (by linarith [Real.add_one_le_exp r]) N
  calc r ^ N * Real.exp (-(r ^ 2) / 2 + c * r)
      ≤ Real.exp (N * r) * Real.exp (-(r ^ 2) / 2 + c * r) := by gcongr
    _ = Real.exp (N * r + (-(r ^ 2) / 2 + c * r)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((c + N) ^ 2 + -(r ^ 2) / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (c + N - r / 2)]
    _ = _ := by rw [Real.exp_add]

private lemma FJ_norm_le (m k : ℕ) (a b : ℂ) (p : ℝ × ℝ) :
    ‖FJ m k a b p‖ ≤ Real.exp ((‖a‖ + ‖b‖ + (m + k : ℕ)) ^ 2) *
      (Real.exp (-(1 / 4) * p.1 ^ 2) * Real.exp (-(1 / 4) * p.2 ^ 2)) := by
  have hr : 0 ≤ ‖zz p‖ := norm_nonneg _
  have hsq := zz_norm_sq p
  unfold FJ
  rw [norm_mul, norm_mul, norm_pow, norm_pow, zb_norm, Complex.norm_exp, ← pow_add]
  have hre : (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + a * zz p + b * zb p).re ≤
      -(‖zz p‖ ^ 2) / 2 + (‖a‖ + ‖b‖) * ‖zz p‖ := by
    have h1 : (a * zz p).re ≤ ‖a‖ * ‖zz p‖ := by
      rw [← norm_mul]; exact Complex.re_le_norm _
    have h2 : (b * zb p).re ≤ ‖b‖ * ‖zz p‖ := by
      rw [← zb_norm, ← norm_mul]; exact Complex.re_le_norm _
    have h3 : (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2).re = -(‖zz p‖ ^ 2) / 2 := by
      rw [hsq]
      have : (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2) = ((-(p.1 ^ 2 + p.2 ^ 2) / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [Complex.add_re, Complex.add_re, h3]; linarith
  calc ‖zz p‖ ^ (m + k) * Real.exp (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + a * zz p + b * zb p).re
      ≤ ‖zz p‖ ^ (m + k) * Real.exp (-(‖zz p‖ ^ 2) / 2 + (‖a‖ + ‖b‖) * ‖zz p‖) := by gcongr
    _ ≤ _ := by
      have hg : Real.exp (-(1 / 4) * p.1 ^ 2) * Real.exp (-(1 / 4) * p.2 ^ 2) =
          Real.exp (-(‖zz p‖ ^ 2) / 4) := by
        rw [← Real.exp_add, hsq]; congr 1; ring
      rw [hg]
      exact real_bound (m + k) (‖a‖ + ‖b‖) ‖zz p‖ hr

private lemma zz_continuous : Continuous zz := by
  unfold zz; fun_prop

private lemma zb_continuous : Continuous zb := by
  unfold zb; fun_prop

private lemma FJ_continuous (m k : ℕ) (a b : ℂ) : Continuous (FJ m k a b) := by
  have h1 := zz_continuous
  have h2 := zb_continuous
  unfold FJ
  fun_prop

private lemma gauss_integrable :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(1 / 4) * p.1 ^ 2) * Real.exp (-(1 / 4) * p.2 ^ 2)) :=
  Integrable.mul_prod (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4))
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4))

private lemma FJ_integrable (m k : ℕ) (a b : ℂ) : Integrable (FJ m k a b) := by
  refine Integrable.mono' (gauss_integrable.const_mul (Real.exp ((‖a‖ + ‖b‖ + (m + k : ℕ)) ^ 2)))
    (FJ_continuous m k a b).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => FJ_norm_le m k a b p

private lemma FJ_hasDerivAt_a (m k : ℕ) (a b : ℂ) (p : ℝ × ℝ) :
    HasDerivAt (fun a => FJ m k a b p) (FJ (m + 1) k a b p) a := by
  unfold FJ
  have h : HasDerivAt
      (fun a : ℂ => -(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + a * zz p + b * zb p) (zz p) a := by
    have := (((hasDerivAt_id a).mul_const (zz p)).const_add
      (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2)).add_const (b * zb p)
    simpa using this
  refine ((h.cexp).const_mul (zz p ^ m * zb p ^ k)).congr_deriv ?_
  ring

private lemma FJ_hasDerivAt_b (m k : ℕ) (a b : ℂ) (p : ℝ × ℝ) :
    HasDerivAt (fun b => FJ m k a b p) (FJ m (k + 1) a b p) b := by
  unfold FJ
  have h : HasDerivAt
      (fun b : ℂ => -(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + a * zz p + b * zb p) (zb p) b := by
    have := ((hasDerivAt_id b).mul_const (zb p)).const_add
      (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + a * zz p)
    simpa using this
  refine ((h.cexp).const_mul (zz p ^ m * zb p ^ k)).congr_deriv ?_
  ring

private lemma ball_norm_le {a x : ℂ} (hx : x ∈ Metric.ball a 1) : ‖x‖ ≤ ‖a‖ + 1 := by
  have h1 : ‖x - a‖ < 1 := by simpa [dist_eq_norm] using hx
  have h2 : ‖x‖ ≤ ‖a‖ + ‖x - a‖ := norm_le_norm_add_norm_sub' x a
  linarith

private lemma J_hasDerivAt_a (m k : ℕ) (a b : ℂ) :
    HasDerivAt (fun a => J m k a b) (J (m + 1) k a b) a := by
  unfold J
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun a p => FJ m k a b p) (F' := fun a p => FJ (m + 1) k a b p) (x₀ := a)
    (s := Metric.ball a 1)
    (bound := fun p => Real.exp ((‖a‖ + 1 + ‖b‖ + (m + 1 + k : ℕ)) ^ 2) *
      (Real.exp (-(1 / 4) * p.1 ^ 2) * Real.exp (-(1 / 4) * p.2 ^ 2)))
    (Metric.ball_mem_nhds a one_pos)
    (Filter.Eventually.of_forall fun x => (FJ_continuous m k x b).aestronglyMeasurable)
    (FJ_integrable m k a b)
    (FJ_continuous (m + 1) k a b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p x hx => ?_)
    (gauss_integrable.const_mul _)
    (Filter.Eventually.of_forall fun p x hx => FJ_hasDerivAt_a m k x b p)).2
  refine (FJ_norm_le (m + 1) k x b p).trans ?_
  have := ball_norm_le hx
  gcongr

private lemma J_hasDerivAt_b (m k : ℕ) (a b : ℂ) :
    HasDerivAt (fun b => J m k a b) (J m (k + 1) a b) b := by
  unfold J
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun b p => FJ m k a b p) (F' := fun b p => FJ m (k + 1) a b p) (x₀ := b)
    (s := Metric.ball b 1)
    (bound := fun p => Real.exp ((‖a‖ + (‖b‖ + 1) + (m + (k + 1) : ℕ)) ^ 2) *
      (Real.exp (-(1 / 4) * p.1 ^ 2) * Real.exp (-(1 / 4) * p.2 ^ 2)))
    (Metric.ball_mem_nhds b one_pos)
    (Filter.Eventually.of_forall fun x => (FJ_continuous m k a x).aestronglyMeasurable)
    (FJ_integrable m k a b)
    (FJ_continuous m (k + 1) a b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p x hx => ?_)
    (gauss_integrable.const_mul _)
    (Filter.Eventually.of_forall fun p x hx => FJ_hasDerivAt_b m k a x p)).2
  refine (FJ_norm_le m (k + 1) a x p).trans ?_
  have := ball_norm_le hx
  gcongr

private lemma J_zero_zero (a b : ℂ) : J 0 0 a b = 2 * Real.pi * Complex.exp (2 * a * b) := by
  unfold J
  have hF : ∀ p : ℝ × ℝ, FJ 0 0 a b p =
      Complex.exp ((-(1 / 2) : ℂ) * (p.1 : ℂ) ^ 2 + (a + b) * (p.1 : ℂ) + 0) *
        Complex.exp ((-(1 / 2) : ℂ) * (p.2 : ℂ) ^ 2 + (Complex.I * (a - b)) * (p.2 : ℂ) + 0) := by
    intro p
    unfold FJ zz zb
    rw [← Complex.exp_add]
    simp only [pow_zero, one_mul]
    congr 1
    push_cast
    ring
  simp_rw [hF]
  have hre : ((-(1 / 2) : ℂ)).re < 0 := by norm_num
  have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => Complex.exp ((-(1 / 2) : ℂ) * (x : ℂ) ^ 2 + (a + b) * (x : ℂ) + 0))
    (fun y : ℝ => Complex.exp ((-(1 / 2) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * (a - b)) * (y : ℂ) + 0))
  rw [Measure.volume_eq_prod, this, integral_cexp_quadratic hre, integral_cexp_quadratic hre]
  have h2 : ((Real.pi : ℂ) / -(-(1 / 2) : ℂ)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / -(-(1 / 2) : ℂ)) ^ (1 / 2 : ℂ) = 2 * Real.pi := by
    have hne : ((Real.pi : ℂ) / -(-(1 / 2) : ℂ)) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this]
    rw [← Complex.cpow_add _ _ hne]
    norm_num
    ring
  calc _ = (((Real.pi : ℂ) / -(-(1 / 2) : ℂ)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / -(-(1 / 2) : ℂ)) ^ (1 / 2 : ℂ)) *
      (Complex.exp (0 - (a + b) ^ 2 / (4 * (-(1 / 2) : ℂ))) *
        Complex.exp (0 - (Complex.I * (a - b)) ^ 2 / (4 * (-(1 / 2) : ℂ)))) := by ring
    _ = _ := by
      rw [h2, ← Complex.exp_add]
      congr 2
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination ((a - b) ^ 2 / 2) * hI

private lemma J_zero_left (k : ℕ) : ∀ a b : ℂ,
    J 0 k a b = 2 * Real.pi * Complex.exp (2 * a * b) * (2 * a) ^ k := by
  induction k with
  | zero => intro a b; rw [J_zero_zero]; simp
  | succ k ih =>
    intro a b
    have h1 := J_hasDerivAt_b 0 k a b
    have h3 : (fun b => J 0 k a b) =
        fun b => 2 * Real.pi * Complex.exp (2 * a * b) * (2 * a) ^ k := funext (ih a)
    rw [h3] at h1
    have h2 : HasDerivAt (fun b : ℂ => 2 * Real.pi * Complex.exp (2 * a * b) * (2 * a) ^ k)
        (2 * Real.pi * (Complex.exp (2 * a * b) * (2 * a * 1)) * (2 * a) ^ k) b :=
      ((((hasDerivAt_id b).const_mul (2 * a)).cexp).const_mul (2 * (Real.pi : ℂ))).mul_const _
    rw [h1.unique h2]
    ring

private lemma J_row (m : ℕ) : ∀ (k : ℕ) (a b : ℂ),
    J (m + 1) k a b = 2 * b * J m k a b + 2 * k * J m (k - 1) a b := by
  induction m with
  | zero =>
    intro k a b
    have h1 := J_hasDerivAt_a 0 k a b
    have h3 : (fun a => J 0 k a b) =
        fun a => 2 * Real.pi * Complex.exp (2 * a * b) * (2 * a) ^ k :=
      funext fun a => J_zero_left k a b
    rw [h3] at h1
    have hA : HasDerivAt (fun a : ℂ => 2 * a * b) (2 * b) a := by
      have := ((hasDerivAt_id a).const_mul (2 : ℂ)).mul_const b
      simpa using this
    have hB : HasDerivAt (fun a : ℂ => (2 * a) ^ k) ((k : ℂ) * (2 * a) ^ (k - 1) * 2) a := by
      have := ((hasDerivAt_id a).const_mul (2 : ℂ)).fun_pow k
      simpa using this
    have h2 := ((hA.cexp).const_mul (2 * (Real.pi : ℂ))).mul hB
    rw [h1.unique h2, J_zero_left, J_zero_left]
    ring
  | succ m ih =>
    intro k a b
    have h1 := J_hasDerivAt_a (m + 1) k a b
    have h3 : (fun a => J (m + 1) k a b) =
        fun a => 2 * b * J m k a b + 2 * k * J m (k - 1) a b := funext fun a => ih k a b
    rw [h3] at h1
    have h2 : HasDerivAt (fun a => 2 * b * J m k a b + 2 * k * J m (k - 1) a b)
        (2 * b * J (m + 1) k a b + 2 * k * J (m + 1) (k - 1) a b) a :=
      ((J_hasDerivAt_a m k a b).const_mul (2 * b)).add
        ((J_hasDerivAt_a m (k - 1) a b).const_mul (2 * (k : ℂ)))
    exact h1.unique h2

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

private lemma disp_eq (z : ℂ) (m n : ℕ) :
    displacementMatrix z m n =
      ((Real.exp (-Complex.normSq z / 2) *
        Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) : ℝ) : ℂ) *
        E2 z (-star z) m n := rfl

private lemma sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Closed form of the Gaussian moments. -/
private lemma J_eq (m : ℕ) : ∀ (k : ℕ) (a b : ℂ),
    J m k a b = 2 * Real.pi * Complex.exp (2 * a * b) *
      ((Real.sqrt 2 : ℂ) ^ (m + k) * (m.factorial : ℂ) * (k.factorial : ℂ)) *
      E2 ((Real.sqrt 2 : ℂ) * b) ((Real.sqrt 2 : ℂ) * a) m k := by
  have hs := sqrt_two_sq
  induction m with
  | zero =>
    intro k a b
    rw [J_zero_left, E2_zero_left]
    have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (2 * a) ^ k = (Real.sqrt 2 : ℂ) ^ k * ((Real.sqrt 2 : ℂ) * a) ^ k := by
      rw [← mul_pow, ← mul_assoc, ← sq, hs]
    rw [h2]
    simp only [zero_add, Nat.factorial_zero, Nat.cast_one, mul_one]
    field_simp
  | succ m ih =>
    intro k a b
    rw [J_row]
    cases k with
    | zero =>
      have hrow := E2_row_zero ((Real.sqrt 2 : ℂ) * b) ((Real.sqrt 2 : ℂ) * a) m
      rw [ih]
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_succ, Nat.factorial_zero]
      linear_combination
        (-(2 * Real.pi * Complex.exp (2 * a * b) * (Real.sqrt 2 : ℂ) ^ (m + 1) *
          (m.factorial : ℂ))) * hrow +
        (-(2 * Real.pi * Complex.exp (2 * a * b) * (Real.sqrt 2 : ℂ) ^ m * (m.factorial : ℂ) * b *
          E2 ((Real.sqrt 2 : ℂ) * b) ((Real.sqrt 2 : ℂ) * a) m 0)) * hs
    | succ k =>
      have hrow := E2_row_succ ((Real.sqrt 2 : ℂ) * b) ((Real.sqrt 2 : ℂ) * a) m k
      rw [ih, ih]
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      linear_combination
        (-(2 * Real.pi * Complex.exp (2 * a * b) * (Real.sqrt 2 : ℂ) ^ (m + k) *
          (m.factorial : ℂ) * ((k : ℂ) + 1) * (k.factorial : ℂ)) *
          (E2 ((Real.sqrt 2 : ℂ) * b) ((Real.sqrt 2 : ℂ) * a) m k +
            b * (Real.sqrt 2 : ℂ) * E2 ((Real.sqrt 2 : ℂ) * b) ((Real.sqrt 2 : ℂ) * a) m (k + 1))) *
          hs +
        (-(2 * Real.pi * Complex.exp (2 * a * b) * (Real.sqrt 2 : ℂ) ^ (m + k) *
          (Real.sqrt 2 : ℂ) ^ 2 * (m.factorial : ℂ) * ((k : ℂ) + 1) * (k.factorial : ℂ))) * hrow

/-! ### The single-mode integrand -/

/-- The single-mode factor of the integrand, at `p = (β_q, β_p)`. -/
private def modeFn (tq tp : ℝ) (m k : ℕ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * ((tq * p.1 + tp * p.2 : ℝ) : ℂ)) *
    (((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 4) : ℝ) : ℂ) *
      ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ m /
      ((Real.sqrt 2 : ℂ) ^ m * (Real.sqrt (Nat.factorial m) : ℂ))) *
    star (((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 4) : ℝ) : ℂ) *
      ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ k /
      ((Real.sqrt 2 : ℂ) ^ k * (Real.sqrt (Nat.factorial k) : ℂ)))

private lemma modeFn_eq (tq tp : ℝ) (m k : ℕ) (p : ℝ × ℝ) :
    modeFn tq tp m k p =
      FJ m k ((Complex.I * tq + tp) / 2) ((Complex.I * tq - tp) / 2) p /
        ((Real.sqrt 2 : ℂ) ^ (m + k) * (Real.sqrt (Nat.factorial m) : ℂ) *
          (Real.sqrt (Nat.factorial k) : ℂ)) := by
  have hstar : star (((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 4) : ℝ) : ℂ) *
      ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ k /
      ((Real.sqrt 2 : ℂ) ^ k * (Real.sqrt (Nat.factorial k) : ℂ))) =
      ((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 4) : ℝ) : ℂ) * zb p ^ k /
      ((Real.sqrt 2 : ℂ) ^ k * (Real.sqrt (Nat.factorial k) : ℂ)) := by
    rw [Complex.star_def, map_div₀, map_mul, map_mul, map_pow, map_pow, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_ofReal]
    congr 3
    simp [zb, sub_eq_add_neg]
  have hexp : Complex.exp (Complex.I * ((tq * p.1 + tp * p.2 : ℝ) : ℂ)) *
      ((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 4) : ℝ) : ℂ) *
      ((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 4) : ℝ) : ℂ) =
      Complex.exp (-(((p.1 ^ 2 + p.2 ^ 2 : ℝ)) : ℂ) / 2 + (Complex.I * tq + tp) / 2 * zz p +
        (Complex.I * tq - tp) / 2 * zb p) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold zz zb
    push_cast
    ring
  unfold modeFn FJ
  rw [hstar, ← hexp]
  unfold zz
  ring

private lemma modeFn_integrable (tq tp : ℝ) (m k : ℕ) : Integrable (modeFn tq tp m k) := by
  have h : modeFn tq tp m k = fun p =>
      FJ m k ((Complex.I * tq + tp) / 2) ((Complex.I * tq - tp) / 2) p /
        ((Real.sqrt 2 : ℂ) ^ (m + k) * (Real.sqrt (Nat.factorial m) : ℂ) *
          (Real.sqrt (Nat.factorial k) : ℂ)) := funext (modeFn_eq tq tp m k)
  rw [h]
  exact (FJ_integrable m k _ _).div_const _

/-- **Single mode.** -/
private lemma modeFn_integral (tq tp : ℝ) (m k : ℕ) :
    ∫ p : ℝ × ℝ, modeFn tq tp m k p =
      ((2 * Real.pi * Real.exp (-(tq ^ 2 + tp ^ 2) / 4) : ℝ) : ℂ) *
        displacementMatrix ((-(tp : ℂ) + Complex.I * (tq : ℂ)) / (Real.sqrt 2 : ℂ)) m k := by
  have hs := sqrt_two_sq
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  simp_rw [modeFn_eq]
  rw [integral_div]
  change J m k _ _ / _ = _
  set ζ : ℂ := (-(tp : ℂ) + Complex.I * (tq : ℂ)) / (Real.sqrt 2 : ℂ) with hζ
  have hb : (Real.sqrt 2 : ℂ) * ((Complex.I * tq - tp) / 2) = ζ := by
    rw [hζ]
    field_simp
    linear_combination (Complex.I * tq - tp) * hs
  have ha : (Real.sqrt 2 : ℂ) * ((Complex.I * tq + tp) / 2) = -star ζ := by
    have hst : star ζ = (-(tp : ℂ) - Complex.I * (tq : ℂ)) / (Real.sqrt 2 : ℂ) := by
      rw [hζ, Complex.star_def, map_div₀, map_add, map_neg, map_mul, Complex.conj_ofReal,
        Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hst]
    field_simp
    linear_combination (Complex.I * tq + tp) * hs
  have hn : Complex.normSq ζ = (tq ^ 2 + tp ^ 2) / 2 := by
    rw [hζ, map_div₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    congr 1
    rw [Complex.normSq_apply]
    simp
    ring
  have hexp : Complex.exp (2 * ((Complex.I * tq + tp) / 2) * ((Complex.I * tq - tp) / 2)) =
      ((Real.exp (-(tq ^ 2 + tp ^ 2) / 4) * Real.exp (-Complex.normSq ζ / 2) : ℝ) : ℂ) := by
    rw [hn, ← Real.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination ((tq : ℂ) ^ 2 / 2) * Complex.I_sq
  have hfm : ∀ n : ℕ, ((n.factorial : ℕ) : ℂ) = ((Real.sqrt (n.factorial : ℝ) : ℝ) : ℂ) ^ 2 := by
    intro n
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hfm0 : ∀ n : ℕ, ((Real.sqrt (n.factorial : ℝ) : ℝ) : ℂ) ≠ 0 := by
    intro n
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos n))).ne'
  have hm0 := hfm0 m
  have hk0 := hfm0 k
  rw [J_eq, disp_eq, ha, hb, hexp, hfm m, hfm k, Real.sqrt_mul (Nat.cast_nonneg _)]
  push_cast
  field_simp

/-! ### Assembling the modes -/

theorem solution {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (u v : Occupation (Fin n)) :
    Integrable (fun β : Fin n ⊕ Fin n → ℝ =>
      Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) * coherentVector β v *
        star (coherentVector β u)) ∧
    ∫ β : Fin n ⊕ Fin n → ℝ, Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) *
        coherentVector β v * star (coherentVector β u) =
      (((2 * Real.pi) ^ n * Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) *
        oscillatorWeylKernel
          (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) v u := by
  let e : (Fin n ⊕ Fin n → ℝ) ≃ᵐ (Fin n → ℝ × ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  have he : MeasurePreserving e volume volume :=
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).trans
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  have happly : ∀ (β : Fin n ⊕ Fin n → ℝ) (j : Fin n),
      e β j = (β (Sum.inl j), β (Sum.inr j)) := fun β j => rfl
  let G : (Fin n → ℝ × ℝ) → ℂ := fun q =>
    ∏ j, modeFn (t (Sum.inl j)) (t (Sum.inr j)) (v j) (u j) (q j)
  have hfun : (fun β : Fin n ⊕ Fin n → ℝ =>
      Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) * coherentVector β v *
        star (coherentVector β u)) = fun β => G (e β) := by
    funext β
    have h1 : Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) =
        ∏ j, Complex.exp (Complex.I *
          ((t (Sum.inl j) * β (Sum.inl j) + t (Sum.inr j) * β (Sum.inr j) : ℝ) : ℂ)) := by
      rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, Fintype.sum_sum_type,
        Finset.sum_add_distrib]
    simp only [G, happly]
    unfold coherentVector modeFn
    rw [h1, star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have hG : Integrable G :=
    Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure (ℝ × ℝ)))
      (f := fun j => modeFn (t (Sum.inl j)) (t (Sum.inr j)) (v j) (u j))
      (fun j => modeFn_integrable _ _ _ _)
  have hGi : ∫ q, G q = ∏ j, ∫ p, modeFn (t (Sum.inl j)) (t (Sum.inr j)) (v j) (u j) p :=
    integral_fintype_prod_volume_eq_prod
      (fun j => modeFn (t (Sum.inl j)) (t (Sum.inr j)) (v j) (u j))
  rw [hfun]
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mpr hG, ?_⟩
  rw [he.integral_comp' G, hGi]
  simp_rw [modeFn_integral]
  have hW : oscillatorWeylKernel
      (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) v u =
      ∏ j, displacementMatrix
        ((-(t (Sum.inr j) : ℂ) + Complex.I * (t (Sum.inl j) : ℂ)) / (Real.sqrt 2 : ℂ))
        (v j) (u j) := by
    unfold oscillatorWeylKernel
    refine Finset.prod_congr rfl fun j _ => ?_
    simp
  have hC : ∏ j : Fin n, (((2 * Real.pi *
      Real.exp (-(t (Sum.inl j) ^ 2 + t (Sum.inr j) ^ 2) / 4) : ℝ)) : ℂ) =
      (((2 * Real.pi) ^ n * Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    congr 2
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, neg_div, Finset.sum_div,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hW, Finset.prod_mul_distrib, hC]
