-- Prove2me | solution 1 for BranchNearRepair.uniform_window_and_core
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T16:15:26.466328+00:00
-- url     : https://prove2.me/submissions/c90ae744-859e-4355-9ed2-6f33b5f7baf0

import Mathlib

namespace BranchNearRepair
lemma pow_distance (z : ℂ) (r : ℝ) (hr : 0≤r) (hz : ‖z-1‖≤r) (n : ℕ) :
    ‖z^n-1‖ ≤ (1+r)^n-1 := by
  have hnz : ‖z‖≤1+r := by
    have h := norm_add_le (z-1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at h
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z^(n+1)-1 = (z^n-1)*z+(z-1) := by ring
    rw [he]
    calc
      _ ≤ ‖(z^n-1)*z‖+‖z-1‖ := norm_add_le _ _
      _ = ‖z^n-1‖*‖z‖+‖z-1‖ := by rw [norm_mul]
      _ ≤ ((1+r)^n-1)*(1+r)+r := by
        exact add_le_add (mul_le_mul ih hnz (norm_nonneg _) (by nlinarith [norm_nonneg (z^n-1)])) hz
      _ = (1+r)^(n+1)-1 := by ring

lemma power_bound (n : ℕ) (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (hnr : (n : ℝ)*r≤1/4) :
    (1+r)^n ≤ 4/3 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ)≤ -r by linarith) n
  have hq : (3/4 : ℝ) ≤ (1-r)^n := by
    simp only [mul_neg, ← sub_eq_add_neg] at hb
    linarith
  have hp : (1+r)^n*(1-r)^n ≤ 1 := by
    rw [← mul_pow]
    have ht : (1+r)*(1-r) ≤ 1 := by nlinarith [sq_nonneg r]
    simpa using pow_le_pow_left₀ (by nlinarith) ht n
  have hm := mul_le_mul_of_nonneg_left hq (by positivity : 0≤(1+r)^n)
  nlinarith

theorem inverse_power_positive (n : ℕ) (hn : 1≤n) (w : ℂ)
    (hw : (n : ℝ)*‖w‖ ≤ 1/8) :
    ‖((1-w)⁻¹)^n-1‖≤1/2 ∧ 1/2≤(((1-w)⁻¹)^n).re := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have hr : ‖w‖≤1/8 := by nlinarith [norm_nonneg w]
  have hnorm : 1-‖w‖≤‖(1 : ℂ)-w‖ := by
    have h := norm_add_le ((1 : ℂ)-w) w
    simp only [sub_add_cancel, norm_one] at h
    linarith
  have hne : (1 : ℂ)-w ≠ 0 := by
    intro he
    rw [he, norm_zero] at hnorm
    linarith
  have he : ((1-w)⁻¹ : ℂ)-1 = w/(1-w) := by field_simp; ring
  have hd : ‖((1-w)⁻¹ : ℂ)-1‖≤2*‖w‖ := by
    rw [he, norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hne)).2
    nlinarith [norm_nonneg w]
  have hp := pow_distance ((1-w)⁻¹) (2*‖w‖) (by positivity) hd n
  have hbound := power_bound n (2*‖w‖) (by positivity) (by linarith) (by linarith)
  have hdist : ‖((1-w)⁻¹)^n-1‖≤1/2 := by linarith
  refine ⟨hdist, ?_⟩
  have hreal := Complex.re_le_norm (1-((1-w)⁻¹)^n)
  rw [norm_sub_rev] at hreal
  simp only [Complex.sub_re, Complex.one_re] at hreal
  linarith
end BranchNearRepair
#print axioms BranchNearRepair.inverse_power_positive

namespace BranchNearRepair
lemma perturbation_bound (x e g : ℝ) (hx : 0<x) (he : |e|≤1/2) (hg : 0≤g) :
    ‖(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ)‖ ≤ (1/4+g)/x := by
  have he2 : e^2≤1/4 := by
    have := abs_le.mp he
    nlinarith
  have hp : |2*e*g|≤g := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ)≤2), abs_of_nonneg hg]
    nlinarith
  have hn := norm_add_le ((e^2 : ℝ) : ℂ) ((2*e*g : ℝ)*Complex.I)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg e), Complex.norm_I, mul_one, abs_of_nonneg hg, abs_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hn
  rw [abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hp
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0<x+g^2)]
  calc
    _ ≤ (1/4+g)/(x+g^2) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ (1/4+g)/x := div_le_div_of_nonneg_left (by positivity) hx (by nlinarith [sq_nonneg g])

theorem near_window_positive (n : ℕ) (hn : 1≤n) (h A e g : ℝ)
    (hh : 0<h) (he : |e|≤1/2) (hg : 0≤g) (hAg : g*h≤A)
    (hsmall : h^2/4+A*h≤1/8) :
    1/2 ≤ (((1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/
       ((n : ℝ)/h^2+g^2 : ℝ))⁻¹)^n).re := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnne : (n : ℝ)≠0 := ne_of_gt hn0
  have hne : h≠0 := ne_of_gt hh
  have hb := perturbation_bound ((n : ℝ)/h^2) e g (by positivity) he hg
  have hm := mul_le_mul_of_nonneg_left hb (le_of_lt hn0)
  have heq : (n : ℝ)*((1/4+g)/((n : ℝ)/h^2)) = h^2/4+(g*h)*h  := by field_simp
  rw [heq] at hm
  have hw : (n : ℝ)*‖(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/((n : ℝ)/h^2+g^2 : ℝ)‖ ≤ 1/8 := by
    nlinarith [mul_le_mul_of_nonneg_right hAg (le_of_lt hh)]
  exact (inverse_power_positive n hn _ hw).2

open Filter Topology

theorem near_window_eventually (k : ℕ → ℕ) (hk : ∀ n, 1≤k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (ht : Tendsto h atTop (𝓝 0)) (A : ℝ) :
    ∀ᶠ n in atTop, ∀ e g : ℝ, |e|≤1/2 → 0≤g → g*h n≤A →
    1/2 ≤ (((1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/
       ((k n : ℝ)/(h n)^2+g^2 : ℝ))⁻¹)^(k n)).re := by
  have hs : Tendsto (fun n => (h n)^2/4+A*h n) atTop (𝓝 (0 : ℝ)) := by
    convert ((ht.pow 2).div_const 4).add (ht.const_mul A) using 1 <;> norm_num
  filter_upwards [hs.eventually_le_const (by norm_num : (0 : ℝ)<1/8)] with n hn
  intro e g he hg hAg
  exact near_window_positive (k n) (hk n) (h n) A e g (hh n) he hg hAg hn
end BranchNearRepair
#print axioms BranchNearRepair.near_window_eventually

namespace BranchNearRepair
lemma ratio_factorization (x e g : ℝ) (hx : 0<x) :
    (x : ℂ)/((x+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I) =
    (x/(x+g^2) : ℝ)*(1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ))⁻¹ := by
  have hd : (x+g^2 : ℝ)≠0 := ne_of_gt (by positivity)
  have hdC : ((x+g^2 : ℝ) : ℂ)≠0 := by exact_mod_cast hd
  have heq : (1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ)) =
      ((x+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ) := by
    rw [one_sub_div hdC]
    congr 1
    push_cast
    ring
  rw [heq, inv_div, Complex.ofReal_div]
  field_simp

theorem near_ratio_lower (n : ℕ) (hn : 1≤n) (h A e g : ℝ)
    (hh : 0<h) (he : |e|≤1/2) (hg : 0≤g) (hAg : g*h≤A)
    (hsmall : h^2/4+A*h≤1/8) :
    (1/2)*(((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2))^n ≤
    (((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^n).re := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp := near_window_positive n hn h A e g hh he hg hAg hsmall
  rw [ratio_factorization _ e g (by positivity), mul_pow]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hp (by positivity : 0≤(((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2))^n)

lemma core_real_lower (n : ℕ) (hn : 1≤n) (h g : ℝ)
    (hh : 0<h) (hg : 0≤g) (hgh : g*h≤1) :
    Real.exp (-1) ≤ (((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2))^n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hne : h≠0 := ne_of_gt hh
  have hnne : (n : ℝ)≠0 := ne_of_gt hn0
  have ht : 0≤g^2*h^2/(n : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ (by positivity : 0≤1+g^2*h^2/(n : ℝ))
    (by simpa [add_comm] using Real.add_one_le_exp (g^2*h^2/(n : ℝ))) n
  rw [← Real.exp_nat_mul] at hpow
  have he : (n : ℝ)*(g^2*h^2/(n : ℝ)) = (g*h)^2 := by field_simp
  rw [he] at hpow
  have hs : (g*h)^2≤1 := by nlinarith [mul_nonneg hg hh.le]
  have hle := hpow.trans (Real.exp_le_exp.mpr hs)
  have hdiv : ((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2) = (1+g^2*h^2/(n : ℝ))⁻¹ := by field_simp
  rw [hdiv, inv_pow, Real.exp_neg]
  exact inv_anti₀ (by positivity) hle
end BranchNearRepair
#print axioms BranchNearRepair.near_ratio_lower
#print axioms BranchNearRepair.core_real_lower

namespace BranchNearRepair
open Filter Topology

theorem uniform_window_and_core (k : ℕ → ℕ) (hk : ∀ n, 1≤k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (ht : Tendsto h atTop (𝓝 0))
    (A : ℝ) (hA : 1≤A) :
    ∀ᶠ n in atTop, ∀ e g : ℝ, |e|≤1/2 → 0≤g → g*h n≤A →
    0 < (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re ∧
    (g*h n≤1 → Real.exp (-1)/2 ≤ (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re) := by
  have hs : Tendsto (fun n => (h n)^2/4+A*h n) atTop (𝓝 (0 : ℝ)) := by
    convert ((ht.pow 2).div_const 4).add (ht.const_mul A) using 1 <;> norm_num
  filter_upwards [hs.eventually_le_const (by norm_num : (0 : ℝ)<1/8)] with n hsmall
  intro e g he hg hAg
  have hn0 : (0 : ℝ)<k n := by exact_mod_cast (show 0<k n by have := hk n; omega)
  have hl := near_ratio_lower (k n) (hk n) (h n) A e g (hh n) he hg hAg hsmall
  constructor
  · apply lt_of_lt_of_le _ hl
    have hh0 := hh n
    positivity
  · intro hcore
    have hc := core_real_lower (k n) (hk n) (h n) g (hh n) hg hcore
    linarith
end BranchNearRepair

theorem solution (k : ℕ → ℕ) (hk : ∀ n, 1≤k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (ht : Filter.Tendsto h Filter.atTop (nhds 0))
    (A : ℝ) (hA : 1≤A) :
    ∀ᶠ n in Filter.atTop, ∀ e g : ℝ, |e|≤1/2 → 0≤g → g*h n≤A →
    0 < (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re ∧
    (g*h n≤1 → Real.exp (-1)/2 ≤ (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re) :=
  BranchNearRepair.uniform_window_and_core k hk h hh ht A hA
#print axioms solution
