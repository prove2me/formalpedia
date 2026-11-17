-- Prove2me | solution 1 for BranchEscapeRepair.complex_ratio_tsum_zero
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:32:29.155344+00:00
-- url     : https://prove2.me/submissions/b652b933-779f-4462-9477-54c6969b1a23

import Mathlib

namespace BranchEscapeRepair

lemma quadratic_binomial (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 + (n : ℝ)*t + ((n : ℝ)*((n : ℝ)-1)/2)*t^2 ≤ (1+t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnn : 0 ≤ (n : ℝ)*((n : ℝ)-1) := by
      cases n with
      | zero => norm_num
      | succ k => simp only [Nat.cast_add, Nat.cast_one]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hc : 0 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*t^3 := mul_nonneg (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+t)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ (1+t) n]
    nlinarith

theorem uniform_ratio_majorant (n : ℕ) (hn : 2 ≤ n) (x d : ℝ)
    (hx : 0 < x) (hxn : x ≤ n) (hd : 0 < d) :
    (x / (x+d))^n ≤ 4 / d^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ d/x := le_of_lt (div_pos hd hx)
  have hbin := quadratic_binomial n (d/x) ht
  have hxx : 0 < x^2 := sq_pos_of_pos hx
  have hnx : x^2 ≤ (n : ℝ)^2 := sq_le_sq₀ (le_of_lt hx) (by positivity) |>.2 hxn
  have hcoef : (n : ℝ)^2 ≤ 2*((n : ℝ)*((n : ℝ)-1)) := by nlinarith
  have hmain : d^2/4 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*(d/x)^2 := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hxx).2
    nlinarith [sq_nonneg d]
  have hpow : d^2/4 ≤ (1+d/x)^n := by
    have : 0 ≤ (n : ℝ)*(d/x) := mul_nonneg (by positivity) ht
    linarith
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hid : x/(x+d) = (1+d/x)⁻¹ := by field_simp
  rw [hid, inv_pow]
  calc
    ((1+d/x)^n)⁻¹ ≤ (d^2/4)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = 4/d^2 := by field_simp

end BranchEscapeRepair
#print axioms BranchEscapeRepair.uniform_ratio_majorant

open Filter Topology
namespace BranchEscapeRepair

lemma ratio_linear_bound (n : ℕ) (hn : 1 ≤ n) (x d : ℝ)
    (hx : 0 < x) (hd : 0 < d) :
    (x/(x+d))^n ≤ (x/(n : ℝ))/d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbin := quadratic_binomial n (d/x) (by positivity)
  have hnn : 0 ≤ (n : ℝ)*((n : ℝ)-1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hquad : 0 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*(d/x)^2 := by positivity
  have hb : (n : ℝ)*d/x ≤ (1+d/x)^n := by
    rw [mul_div_assoc]
    linarith
  have hid : x/(x+d) = (1+d/x)⁻¹ := by field_simp
  rw [hid, inv_pow]
  calc
    ((1+d/x)^n)⁻¹ ≤ ((n : ℝ)*d/x)⁻¹ := inv_anti₀ (by positivity) hb
    _ = (x/(n : ℝ))/d := by field_simp

theorem ratio_tsum_tendsto_zero {ι : Type*} (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hs : Summable (fun i => 1/(d i)^2)) (X : ℕ → ℝ)
    (hx : ∀ n, 0 < X n)
    (hlim : Tendsto (fun n => X n/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, (X n/(X n+d i))^n) atTop (𝓝 0) := by
  have hpoint : ∀ i, Tendsto (fun n => (X n/(X n+d i))^n) atTop (𝓝 0) := by
    intro i
    have hh := hlim.div_const (d i)
    simp only [zero_div] at hh
    apply squeeze_zero' _ _ hh
    · exact Filter.Eventually.of_forall (fun n => pow_nonneg (le_of_lt (div_pos (hx n) (add_pos (hx n) (hd i)))) n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact ratio_linear_bound n hn (X n) (d i) (hx n) (hd i)
  have he : ∀ᶠ n : ℕ in atTop, X n ≤ n := by
    have hl : ∀ᶠ n in atTop, X n/(n : ℝ) < 1 := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hl, eventually_ge_atTop 1] with n hh hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact le_of_lt (by simpa using (div_lt_iff₀ hnR).mp hh)
  have hb : ∀ᶠ n : ℕ in atTop, ∀ i, ‖(X n/(X n+d i))^n‖ ≤ 4*(1/(d i)^2) := by
    filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (div_pos (hx n) (add_pos (hx n) (hd i)))) n)]
    simpa only [mul_one_div] using uniform_ratio_majorant n hn2 (X n) (d i) (hx n) hn (hd i)
  have ht := tendsto_tsum_of_dominated_convergence (hs.mul_left 4) hpoint hb
  simpa using ht
end BranchEscapeRepair

namespace BranchEscapeRepair
lemma complex_ratio_norm (n : ℕ) (x d b : ℝ) (hx : 0 < x) (hd : 0 < d) :
    ‖((x : ℂ) / ((x+d : ℝ) + b*Complex.I))^n‖ ≤ (x/(x+d))^n := by
  have hh := Complex.abs_re_le_norm ((x+d : ℝ) + (b : ℂ)*Complex.I)
  have hp : 0 < x+d := add_pos hx hd
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
    abs_of_pos hp] at hh
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (le_of_lt hx) hp hh) n

theorem complex_ratio_tsum_zero {ι : Type*} (d b : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hs : Summable (fun i => 1/(d i)^2)) (X : ℕ → ℝ)
    (hx : ∀ n, 0 < X n)
    (hlim : Tendsto (fun n => X n/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, ((X n : ℂ)/((X n+d i : ℝ)+(b i : ℂ)*Complex.I))^n)
      atTop (𝓝 0) := by
  have he : ∀ᶠ n : ℕ in atTop, X n ≤ n := by
    have hl : ∀ᶠ n in atTop, X n/(n : ℝ) < 1 := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hl, eventually_ge_atTop 1] with n hh hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact le_of_lt (by simpa using (div_lt_iff₀ hnR).mp hh)
  have hp : ∀ i, Tendsto (fun n => ((X n : ℂ)/((X n+d i : ℝ)+(b i : ℂ)*Complex.I))^n) atTop (𝓝 0) := by
    intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := hlim.div_const (d i)
    simp only [zero_div] at hh
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) _ hh
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (complex_ratio_norm n (X n) (d i) (b i) (hx n) (hd i)).trans
      (ratio_linear_bound n hn (X n) (d i) (hx n) (hd i))
  have hb : ∀ᶠ n : ℕ in atTop, ∀ i,
      ‖((X n : ℂ)/((X n+d i : ℝ)+(b i : ℂ)*Complex.I))^n‖ ≤ 4*(1/(d i)^2) := by
    filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
    intro i
    have h := (complex_ratio_norm n (X n) (d i) (b i) (hx n) (hd i)).trans
      (uniform_ratio_majorant n hn2 (X n) (d i) (hx n) hn (hd i))
    simpa only [mul_one_div] using h
  simpa using tendsto_tsum_of_dominated_convergence (hs.mul_left 4) hp hb
end BranchEscapeRepair

theorem solution {ι : Type*} (d b : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hs : Summable (fun i => 1/(d i)^2)) (X : ℕ → ℝ)
    (hx : ∀ n, 0 < X n)
    (hlim : Tendsto (fun n => X n/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, ((X n : ℂ)/((X n+d i : ℝ)+(b i : ℂ)*Complex.I))^n)
      atTop (𝓝 0) := BranchEscapeRepair.complex_ratio_tsum_zero d b hd hs X hx hlim
#print axioms solution
