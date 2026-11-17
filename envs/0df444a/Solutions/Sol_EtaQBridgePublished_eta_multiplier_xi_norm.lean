-- Prove2me | solution 1 for EtaQBridgePublished.eta_multiplier_xi_norm
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T07:15:22.193905+00:00
-- url     : https://prove2.me/submissions/849a295d-cdb6-4eee-a5bc-5c489aaff015

import Mathlib

set_option maxRecDepth 4000

open scoped BigOperators
open Filter Topology

namespace EtaQBridge

-- This definition includes the removable values at s = 0 and s = 1.
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  have hz := differentiable_completedZeta₀
  unfold xi
  fun_prop

theorem xi_functional_equation (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

theorem xi_centered_even (u : ℂ) : xi (1/2-u) = xi (1/2+u) := by
  convert xi_functional_equation (1/2+u) using 1 <;> congr 1 <;> ring

theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  <;> ring

theorem xi_eq_zeta (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s-1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hr
  field_simp

-- The eta multiplier is explicit. The ordered-series identification is a
-- separate analytic obligation, not assumed proved by this definition.
noncomputable def etaViaZeta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ)^(1-s)) * riemannZeta s

theorem eta_xi_norm_identity (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    Complex.normSq (s*(s-1)*Complex.Gammaℝ s) * Complex.normSq (etaViaZeta s) =
      4 * Complex.normSq (1-(2 : ℂ)^(1-s)) * Complex.normSq (xi s) := by
  have he : s*(s-1)*Complex.Gammaℝ s * etaViaZeta s =
      2*(1-(2 : ℂ)^(1-s))*xi s := by
    rw [xi_eq_zeta s hr h1]
    unfold etaViaZeta
    ring
  have hh := congrArg Complex.normSq he
  simp only [map_mul, Complex.normSq_ofNat] at hh ⊢
  nlinarith [hh]

theorem double_cosine_square {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * Real.cos (θ i - θ j)) =
      (∑ i ∈ s, a i * Real.cos (θ i))^2 +
      (∑ i ∈ s, a i * Real.sin (θ i))^2 := by
  simp only [Real.cos_sub, mul_add, pow_two, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

theorem double_cosine_nonnegative {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * Real.cos (θ i - θ j) := by
  rw [double_cosine_square]
  positivity

theorem cosine_square_limit (a θ : ℕ → ℝ) (A B : ℝ)
    (hc : Tendsto (fun N => ∑ i ∈ Finset.range N, a i * Real.cos (θ i)) atTop (𝓝 A))
    (hs : Tendsto (fun N => ∑ i ∈ Finset.range N, a i * Real.sin (θ i)) atTop (𝓝 B)) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      a i * a j * Real.cos (θ i - θ j)) atTop (𝓝 (A^2+B^2)) := by
  simp_rw [double_cosine_square]
  exact (hc.pow 2).add (hs.pow 2)

theorem cosine_square_complex_norm {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * Real.cos (θ i - θ j)) =
      Complex.normSq (∑ i ∈ s,
        (a i : ℂ) * ((Real.cos (θ i) : ℂ) + (Real.sin (θ i) : ℂ) * Complex.I)) := by
  rw [double_cosine_square]
  simp [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
  rfl

-- Exact change of normalization, with n = r + 1 to avoid n = 0.
theorem derivative_to_pole_normalization (r : ℕ) (u D R : ℝ)
    (h : D = (-1 : ℝ)^r * (r.factorial : ℝ) * R) :
    (2 : ℝ)^(r+1) * u^(2*(r+1)-1) * (-1 : ℝ)^r * D =
      (2 : ℝ)^(r+1) * u^(2*(r+1)-1) * (r.factorial : ℝ) * R := by
  rw [h]
  have hsign : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((2 : ℝ)^(r+1) * u^(2*(r+1)-1) * (r.factorial : ℝ) * R) *
      ((-1 : ℝ)^r * (-1 : ℝ)^r) := by ring
    _ = _ := by rw [hsign, mul_one]

-- Pascal relation, valid for complex atoms: no real-spectrum assumption.
theorem tower_atom_pascal (y : ℂ) (p q : ℕ) :
    y^p * (1-y)^q = y^(p+1) * (1-y)^q + y^p * (1-y)^(q+1) := by
  simp only [pow_succ]
  ring

theorem tower_atom_finite_difference (y : ℂ) (p q : ℕ) :
    y^p * (1-y)^q =
      ∑ j ∈ Finset.range (q+1), (-1 : ℂ)^j * (q.choose j : ℂ) * y^(p+j) := by
  rw [sub_eq_add_neg, add_comm (1 : ℂ) (-y), add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -y = (-1 : ℂ) * y by ring, mul_pow, pow_add]
  ring

theorem tower_finite_difference (y : ℕ → ℂ) (p q : ℕ)
    (h : ∀ j ∈ Finset.range (q+1), Summable (fun i => (y i)^(p+j))) :
    (∑' i, (y i)^p * (1-y i)^q) =
      ∑ j ∈ Finset.range (q+1), (-1 : ℂ)^j * (q.choose j : ℂ) *
        (∑' i, (y i)^(p+j)) := by
  simp_rw [tower_atom_finite_difference]
  have hs : ∀ j ∈ Finset.range (q+1),
      Summable (fun i => (-1 : ℂ)^j * (q.choose j : ℂ) * (y i)^(p+j)) := by
    intro j hj
    exact (h j hj).mul_left _
  rw [Summable.tsum_finsetSum hs]
  apply Finset.sum_congr rfl
  intro j hj
  exact tsum_mul_left

theorem moment_resolvent_scaling (B : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    (∑' i, (((u : ℂ)^2 / ((u : ℂ)^2+B i))^n).re) =
      u^(2*n) * ∑' i, ((((u : ℂ)^2+B i)⁻¹)^n).re := by
  have h : ∀ i, (((u : ℂ)^2 / ((u : ℂ)^2+B i))^n).re =
      u^(2*n) * ((((u : ℂ)^2+B i)⁻¹)^n).re := by
    intro i
    rw [div_eq_mul_inv, mul_pow, ← pow_mul]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  simp_rw [h]
  exact tsum_mul_left

end EtaQBridge


theorem solution (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    Complex.normSq (s*(s-1)*Complex.Gammaℝ s) *
      Complex.normSq ((1-(2 : ℂ)^(1-s))*riemannZeta s) =
    4*Complex.normSq (1-(2 : ℂ)^(1-s)) *
      Complex.normSq ((1+s*(s-1)*completedRiemannZeta₀ s)/2) := by
  exact EtaQBridge.eta_xi_norm_identity s hr h1
