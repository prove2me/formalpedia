-- Prove2me | solution 1 for BranchTailRepair.integrated_tail
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:56:37.362787+00:00
-- url     : https://prove2.me/submissions/ae5dc018-9841-4426-bca7-862db1c4f445

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

open MeasureTheory Set
namespace BranchTailRepair
lemma kernel_bound (n : ℕ) (hn : 2 ≤ n) (l y : ℝ)
    (hl : l ≤ 1) (hy : 1 ≤ y) :
    ((1+(y^2-l/4)/(n : ℝ))^n)⁻¹ ≤ 16/y^4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hy0 : 0<y := by linarith
  have hd : 0<y^2/2 := by positivity
  have h := BranchEscapeRepair.uniform_ratio_majorant n hn (n : ℝ) (y^2/2) hn0 le_rfl hd
  have hh : 1+(y^2/2)/(n : ℝ) ≤ 1+(y^2-l/4)/(n : ℝ) := by
    apply add_le_add_right
    apply (div_le_div_iff_of_pos_right hn0).2
    nlinarith [sq_nonneg (y-1)]
  have hp : (1+(y^2/2)/(n : ℝ))^n ≤ (1+(y^2-l/4)/(n : ℝ))^n :=
    pow_le_pow_left₀ (by positivity) hh n
  have hid : ((n : ℝ)/((n : ℝ)+y^2/2))^n = ((1+(y^2/2)/(n : ℝ))^n)⁻¹ := by
    rw [← inv_pow]
    congr 1
    field_simp
  rw [hid] at h
  have hh2 := (inv_anti₀ (by positivity : 0 < (1+(y^2/2)/(n : ℝ))^n) hp).trans h
  have heq : 4 / (y^2/2)^2 = 16/y^4 := by field_simp; ring
  rwa [heq] at hh2

lemma weighted_bound (n : ℕ) (hn : 2 ≤ n) (l L y : ℝ)
    (hl : l ≤ 1) (hL : 1 ≤ L) (hy : 1 ≤ y) :
    0 ≤ (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹ ∧
    (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹ ≤ 64*L/y^3 := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hy0 : 0<y := by linarith
  have hlog0 : 0 ≤ Real.log (y+3) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0<y+3)
  have hweight : L+Real.log (y+3) ≤ 4*L*y := by
    nlinarith [mul_nonneg (show 0≤L-1 by linarith) (show 0≤y-1 by linarith)]
  have hbase : 0 < 1+(y^2-l/4)/(n : ℝ) := by
    have : 0 ≤ y^2-l/4 := by nlinarith [sq_nonneg (y-1)]
    positivity
  constructor
  · positivity
  · calc
      _ ≤ (4*L*y)*(16/y^4) := mul_le_mul hweight (kernel_bound n hn l y hl hy)
        (by positivity) (by positivity)
      _ = 64*L/y^3 := by field_simp; ring

theorem integrated_tail (n : ℕ) (hn : 2 ≤ n) (l L M : ℝ)
    (hl : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M) :
    IntegrableOn (fun y : ℝ => (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) (Ioi M) ∧
    (∫ y : ℝ in Ioi M, (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) ≤ 32*L/M^2 := by
  have hM0 : 0<M := by linarith
  have hpow : ∀ y : ℝ, y^(-3 : ℝ) = 1/y^3 := by
    intro y
    convert Real.rpow_intCast y (-3) using 1 <;> norm_num
  have hg : IntegrableOn (fun y : ℝ => 64*L/y^3) (Ioi M) := by
    have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ)< -1) hM0).const_mul (64*L)
    change Integrable (fun y : ℝ => 64*L/y^3) (volume.restrict (Ioi M))
    convert h using 1 <;> funext y <;> rw [hpow] <;> ring
  have hbound : ∀ᵐ y : ℝ ∂volume.restrict (Ioi M),
      ‖(L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹‖ ≤ 64*L/y^3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have h := weighted_bound n hn l L y hl hL (le_trans hM (le_of_lt hy))
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hf : IntegrableOn (fun y : ℝ => (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) (Ioi M) :=
    hg.mono' (by fun_prop) hbound
  refine ⟨hf, ?_⟩
  have hle := integral_mono_ae hf hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (weighted_bound n hn l L y hl hL (le_trans hM (le_of_lt hy))).2)
  have heq : (∫ y : ℝ in Ioi M, 64*L/y^3) = 32*L/M^2 := by
    have hfun : (fun y : ℝ => 64*L/y^3) = (fun y : ℝ => 64*L*y^(-3 : ℝ)) := by
      funext y
      rw [hpow]
      ring
    rw [hfun, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hM0]
    have hp2 : M^(-2 : ℝ) = 1/M^2 := by
      convert Real.rpow_intCast M (-2) using 1 <;> norm_num
    norm_num only at *
    rw [hp2]
    ring
  rwa [heq] at hle
end BranchTailRepair

theorem solution (n : ℕ) (hn : 2 ≤ n) (l L M : ℝ)
    (hl : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M) :
    IntegrableOn (fun y : ℝ => (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) (Ioi M) ∧
    (∫ y : ℝ in Ioi M, (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) ≤ 32*L/M^2 :=
  BranchTailRepair.integrated_tail n hn l L M hl hL hM
#print axioms solution
