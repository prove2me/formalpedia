-- Prove2me | solution 1 for BranchLargeScaleRepair.normalized_pole_sum_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T17:35:30.038797+00:00
-- url     : https://prove2.me/submissions/f6b29521-7717-44ad-9d14-ca3de8b56407

import Mathlib

namespace BranchLargeScaleRepair

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


open Filter Topology

lemma ratio_le_linear_inverse (n : ℕ) (x d : ℝ) (hx : 0 < x) (hd : 0 < d) :
    (x / (x+d))^n ≤ (1 + d*((n : ℝ)/x))⁻¹ := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ d/x by linarith [div_pos hd hx]) n
  have hi : (x / (x+d))^n = ((1+d/x)^n)⁻¹ := by
    rw [← inv_pow]
    congr 1
    field_simp
  rw [hi]
  have he : 1+(n : ℝ)*(d/x) = 1+d*((n : ℝ)/x) := by ring
  rw [he] at hb
  exact inv_anti₀ (by positivity) hb

lemma ratio_tendsto_zero (x : ℕ → ℝ) (hx : ∀ n, 0 < x n) (d : ℝ) (hd : 0 < d)
    (hscale : Tendsto (fun (n : ℕ) => (n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => (x n/(x n+d))^n) atTop (𝓝 0) := by
  have ht := (Tendsto.const_mul_atTop hd hscale).atTop_add
    (tendsto_const_nhds (x := (1 : ℝ)))
  have hi : Tendsto (fun (n : ℕ) => (1+d*((n : ℝ)/x n))⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, add_comm] using tendsto_inv_atTop_zero.comp ht
  exact squeeze_zero (fun (n : ℕ) => by have := hx n; positivity)
    (fun (n : ℕ) => ratio_le_linear_inverse n (x n) d (hx n) hd) hi

/-- Normalized positive-kernel sum tends to zero in the large-scale regime.
No assertion of a uniform exponential rate is used. -/
theorem large_scale_normalized_sum_zero {ι : Type*} (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hs : Summable (fun i => 1/(d i)^2))
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i, (x n/(x n+d i))^n) atTop (𝓝 0) := by
  have hsum : Summable (fun i => 4/(d i)^2) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hs.mul_left 4
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ i, ‖(x n/(x n+d i))^n‖ ≤ 4/(d i)^2 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hscale.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hscale_n i
    have hxn : x n ≤ (n : ℝ) := by
      have hh := (le_div_iff₀ (hx n)).1 hscale_n
      simpa using hh
    rw [Real.norm_of_nonneg (by have := hx n; have := hd i; positivity)]
    exact uniform_ratio_majorant n hn (x n) (d i) (hx n) hxn (hd i)
  have ht := tendsto_tsum_of_dominated_convergence (g := fun _ : ι => (0 : ℝ))
    hsum (fun i => ratio_tendsto_zero x hx (d i) (hd i) hscale) hbound
  simpa using ht


lemma normalized_complex_sum_zero {ι : Type*} (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hs : Summable (fun i => 1/(d i)^2))
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (n : ℝ)/x n) atTop atTop)
    (f : ℕ → ι → ℂ) (hf : ∀ n i, ‖f n i‖ ≤ (x n/(x n+d i))^n) :
    Tendsto (fun n => ∑' i, f n i) atTop (𝓝 0) := by
  have hsum : Summable (fun i => 4/(d i)^2) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hs.mul_left 4
  have hp : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 0) := by
    intro i
    exact squeeze_zero_norm (fun n => hf n i) (ratio_tendsto_zero x hx (d i) (hd i) hscale)
  have hb : ∀ᶠ n : ℕ in atTop, ∀ i, ‖f n i‖ ≤ 4/(d i)^2 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hscale.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hscale_n i
    have hxn : x n ≤ (n : ℝ) := by
      have hh := (le_div_iff₀ (hx n)).1 hscale_n
      simpa using hh
    exact (hf n i).trans (uniform_ratio_majorant n hn (x n) (d i) (hx n) hxn (hd i))
  simpa using tendsto_tsum_of_dominated_convergence (g := fun _ : ι => (0 : ℂ)) hsum hp hb

/-- Large-scale escape estimate for a complex pole family strictly to the right
of an anchor, normalized by the anchor kernel. -/
theorem normalized_pole_sum_tendsto_zero {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).re) (hs : Summable (fun i => 1/((z i).re)^2))
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i, ((x n : ℂ)/((x n : ℂ)+z i))^n) atTop (𝓝 0) := by
  apply normalized_complex_sum_zero (fun i => (z i).re) hz hs x hx hscale
  intro n i
  have hpos : 0 < x n+(z i).re := add_pos (hx n) (hz i)
  have hnorm : x n+(z i).re ≤ ‖(x n : ℂ)+z i‖ := by
    simpa only [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm ((x n : ℂ)+z i)
  have hratio : ‖(x n : ℂ)/((x n : ℂ)+z i)‖ ≤ x n/(x n+(z i).re) := by
    rw [norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hx n)]
    exact div_le_div_of_nonneg_left (le_of_lt (hx n)) hpos hnorm
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hratio n
end BranchLargeScaleRepair

theorem solution {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).re) (hs : Summable (fun i => 1/((z i).re)^2))
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Filter.Tendsto (fun (n : ℕ) => (n : ℝ)/x n) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun (n : ℕ) => ∑' i, ((x n : ℂ)/((x n : ℂ)+z i))^n) Filter.atTop (nhds 0) :=
  BranchLargeScaleRepair.normalized_pole_sum_tendsto_zero z hz hs x hx hscale
