-- Prove2me | solution 2 for ErlerGross.B3_digamma_triplication_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:56:43.414297+00:00
-- url     : https://prove2.me/submissions/2051d998-024c-409b-acd3-ad9b87d651f0

import Mathlib

set_option autoImplicit false

namespace P2MDigammaMul

open Set Filter Topology

noncomputable def gm (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) ^ (x - 1) * ∏ k ∈ Finset.range n, Real.Gamma ((x + k) / n)

lemma gm_pos {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) : 0 < gm n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  unfold gm
  apply mul_pos (Real.rpow_pos_of_pos hn' _)
  apply Finset.prod_pos
  intro k _
  apply Real.Gamma_pos_of_pos
  apply div_pos (by positivity) hn'

lemma gm_add_one {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    gm n (x + 1) = x * gm n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set f : ℕ → ℝ := fun k => Real.Gamma ((x + k) / n) with hf
  have h1 : ∏ k ∈ Finset.range n, Real.Gamma ((x + 1 + k) / n)
      = ∏ k ∈ Finset.range n, f (k + 1) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [hf]
    dsimp only
    push_cast
    ring_nf
  have h2 := Finset.prod_range_succ' f n
  have h3 := Finset.prod_range_succ f n
  have hfn : f n = x / n * f 0 := by
    rw [hf]
    dsimp only
    rw [Nat.cast_zero, add_zero, show (x + n) / n = x / n + 1 by field_simp]
    exact Real.Gamma_add_one (div_pos hx hn').ne'
  have hf0 : f 0 ≠ 0 := by
    rw [hf]
    dsimp only
    rw [Nat.cast_zero, add_zero]
    exact (Real.Gamma_pos_of_pos (div_pos hx hn')).ne'
  have key : ∏ k ∈ Finset.range n, f (k + 1) = (∏ k ∈ Finset.range n, f k) * (x / n) := by
    have := h2.symm.trans h3
    rw [hfn] at this
    apply mul_right_cancel₀ hf0
    rw [this]
    ring
  unfold gm
  have hfk : ∏ k ∈ Finset.range n, f k = ∏ k ∈ Finset.range n, Real.Gamma ((x + k) / n) := rfl
  rw [h1, key, hfk, show x + 1 - 1 = (x - 1) + 1 by ring, Real.rpow_add hn', Real.rpow_one]
  field_simp

lemma convex_comp_affine {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) {a b : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) : ConvexOn ℝ (Ioi 0) (fun x => f (a * x + b)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hx' : a * x + b ∈ Ioi (0:ℝ) := by
    simp only [mem_Ioi] at hx ⊢
    positivity
  have hy' : a * y + b ∈ Ioi (0:ℝ) := by
    simp only [mem_Ioi] at hy ⊢
    positivity
  have := hf.2 hx' hy' hp hq hpq
  simp only [smul_eq_mul] at this ⊢
  have e : a * (p * x + q * y) + b = p * (a * x + b) + q * (a * y + b) := by
    linear_combination (-b) * hpq
  rw [e]
  exact this

lemma convex_sum {ι : Type} (s : Finset ι) (g : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, ConvexOn ℝ (Ioi (0:ℝ)) (g i)) :
    ConvexOn ℝ (Ioi (0:ℝ)) (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact convexOn_const 0 (convex_Ioi 0)
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma log_gm {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    Real.log (gm n x) = (x - 1) * Real.log n +
      ∑ k ∈ Finset.range n, Real.log (Real.Gamma ((1 / (n:ℝ)) * x + k / n)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hp : ∀ k ∈ Finset.range n, 0 < Real.Gamma ((x + k) / n) := by
    intro k _
    exact Real.Gamma_pos_of_pos (by positivity)
  have hP : 0 < ∏ k ∈ Finset.range n, Real.Gamma ((x + k) / n) := Finset.prod_pos hp
  unfold gm
  rw [Real.log_mul (Real.rpow_pos_of_pos hn' _).ne' hP.ne', Real.log_rpow hn',
    Real.log_prod (fun k hk => (hp k hk).ne')]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  field_simp

lemma gm_log_convex {n : ℕ} (hn : 0 < n) : ConvexOn ℝ (Ioi 0) (Real.log ∘ gm n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hlin : ConvexOn ℝ (Ioi (0:ℝ)) (fun x : ℝ => (x - 1) * Real.log n) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    apply le_of_eq
    linear_combination (Real.log n) * hab
  have hc : ConvexOn ℝ (Ioi (0:ℝ)) (fun x => (x - 1) * Real.log n +
      ∑ k ∈ Finset.range n, Real.log (Real.Gamma ((1 / (n:ℝ)) * x + k / n))) := by
    refine hlin.add ?_
    apply convex_sum (Finset.range n)
      (fun k x => Real.log (Real.Gamma ((1 / (n:ℝ)) * x + k / n)))
    intro k _
    have := convex_comp_affine Real.convexOn_log_Gamma (a := 1 / (n:ℝ)) (b := (k:ℝ) / n)
      (by positivity) (by positivity)
    exact this
  refine hc.congr ?_
  intro x hx
  simp only [Function.comp_apply]
  exact (log_gm hn hx).symm

lemma gm_eq {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    gm n x = gm n 1 * Real.Gamma x := by
  have h1 := gm_pos hn one_pos
  have hconv : ConvexOn ℝ (Ioi 0) (Real.log ∘ fun y => gm n y / gm n 1) := by
    refine ((gm_log_convex hn).add_const (-Real.log (gm n 1))).congr ?_
    intro y hy
    simp only [Function.comp_apply, Pi.add_apply]
    rw [Real.log_div (gm_pos hn hy).ne' h1.ne']
    ring
  have := Real.eq_Gamma_of_log_convex (f := fun y => gm n y / gm n 1) hconv
    (fun {y} hy => by
      show gm n (y + 1) / gm n 1 = y * (gm n y / gm n 1)
      rw [gm_add_one hn hy]
      ring)
    (fun {y} hy => div_pos (gm_pos hn hy) h1)
    (div_self h1.ne') hx
  have this' : gm n x / gm n 1 = Real.Gamma x := this
  rw [div_eq_iff h1.ne'] at this'
  rw [this']
  ring

lemma real_mult {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    Real.Gamma (n * t) * gm n 1 =
      (n : ℝ) ^ ((n : ℝ) * t - 1) * ∏ k ∈ Finset.range n, Real.Gamma (t + k / n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have := gm_eq hn (mul_pos hn' ht)
  unfold gm at this
  have e : ∀ k ∈ Finset.range n, Real.Gamma ((n * t + k) / n) = Real.Gamma (t + k / n) := by
    intro k _
    congr 1
    field_simp
  rw [Finset.prod_congr rfl e] at this
  rw [this]
  unfold gm
  ring

lemma re_pos_ne_neg_nat {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s ≠ -m := by
  intro m h
  rw [h] at hs
  simp at hs
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma cplx_ident {n : ℕ} (hn : 0 < n) (z : ℂ) :
    ((n : ℂ) ^ ((n : ℂ) * z - 1))⁻¹ * ∏ k ∈ Finset.range n, (Complex.Gamma (z + (k : ℂ) / n))⁻¹
      = (((gm n 1 : ℝ) : ℂ))⁻¹ * (Complex.Gamma ((n : ℂ) * z))⁻¹ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : AnalyticOnNhd ℂ (fun z : ℂ => ((n : ℂ) ^ ((n : ℂ) * z - 1))⁻¹ *
      ∏ k ∈ Finset.range n, (Complex.Gamma (z + (k : ℂ) / n))⁻¹) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine Differentiable.differentiableOn ?_
    apply Differentiable.mul
    · refine fun t => DifferentiableAt.inv ?_ (Complex.cpow_ne_zero_iff.mpr (Or.inl hnc))
      refine DifferentiableAt.const_cpow ?_ (Or.inl hnc)
      exact DifferentiableAt.sub_const (differentiableAt_id.const_mul _) _
    · apply Differentiable.fun_finsetProd
      intro k _
      exact Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add (differentiable_const _))
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ => (((gm n 1 : ℝ) : ℂ))⁻¹ *
      (Complex.Gamma ((n : ℂ) * z))⁻¹) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine Differentiable.differentiableOn ?_
    apply Differentiable.mul (differentiable_const _)
    exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.const_mul _)
  have h3 : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]; constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr
        (Eventually.of_forall fun t ht => Complex.ofReal_ne_one.mpr ht)
  have := AnalyticOnNhd.eq_of_frequently_eq h1 h2 (h3.frequently ?_)
  · exact congr_fun this z
  refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
  refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht => ?_)
  have hr := real_mult hn ht
  have hG : Real.Gamma (n * t) ≠ 0 := (Real.Gamma_pos_of_pos (mul_pos hn' ht)).ne'
  have hP : ∀ k ∈ Finset.range n, Real.Gamma (t + k / n) ≠ 0 := by
    intro k _
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hreal : ((n : ℝ) ^ ((n : ℝ) * t - 1))⁻¹ * ∏ k ∈ Finset.range n, (Real.Gamma (t + k / n))⁻¹
      = (gm n 1)⁻¹ * (Real.Gamma (n * t))⁻¹ := by
    rw [Finset.prod_inv_distrib, ← mul_inv, ← hr, mul_inv, mul_comm]
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_inv,
    Complex.ofReal_cpow hn'.le, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_natCast] at hc
  have eG : ∀ k ∈ Finset.range n, ((Real.Gamma (t + k / n) : ℝ) : ℂ)
      = Complex.Gamma ((t : ℂ) + (k : ℂ) / n) := by
    intro k _
    rw [← Complex.Gamma_ofReal]
    push_cast
    rfl
  have eG2 : ((Real.Gamma (n * t) : ℝ) : ℂ) = Complex.Gamma ((n : ℂ) * t) := by
    rw [← Complex.Gamma_ofReal]
    push_cast
    rfl
  rw [Finset.prod_congr rfl (fun k hk => by rw [eG k hk]), eG2] at hc
  exact hc

lemma cplx_mult {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma ((n : ℂ) * z) =
      (n : ℂ) ^ ((n : ℂ) * z - 1) * (∏ k ∈ Finset.range n, Complex.Gamma (z + (k : ℂ) / n)) *
        (((gm n 1 : ℝ) : ℂ))⁻¹ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hc : ((gm n 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (gm_pos hn one_pos).ne'
  have hre : 0 < ((n : ℂ) * z).re := by
    simp [Complex.mul_re]
    positivity
  have hG : Complex.Gamma ((n : ℂ) * z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hP : ∏ k ∈ Finset.range n, Complex.Gamma (z + (k : ℂ) / n) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [show (k : ℂ) / (n : ℂ) = (((k : ℝ) / n : ℝ) : ℂ) by push_cast; rfl, Complex.add_re,
      Complex.ofReal_re]
    positivity
  have hAne : (n : ℂ) ^ ((n : ℂ) * z - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn.ne'))
  have := cplx_ident hn z
  rw [Finset.prod_inv_distrib] at this
  field_simp at this ⊢
  linear_combination this

theorem mult_formula (n : Nat) (hn : 0 < n) (z : Complex) (hz : 0 < z.re) :
    Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
      n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (((gm n 1 : ℝ) : ℂ))⁻¹ ≠ 0 := by
    have : ((gm n 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (gm_pos hn one_pos).ne'
    exact inv_ne_zero this
  have hkre : ∀ w : ℂ, 0 < w.re → ∀ k : ℕ, 0 < (w + (k : ℂ) / n).re := by
    intro w hw k
    rw [show (k : ℂ) / (n : ℂ) = (((k : ℝ) / n : ℝ) : ℂ) by push_cast; rfl, Complex.add_re,
      Complex.ofReal_re]
    positivity
  -- local equality of functions near z
  have hev : (fun w : ℂ => Complex.Gamma ((n : ℂ) * w)) =ᶠ[𝓝 z]
      (fun w : ℂ => (n : ℂ) ^ ((n : ℂ) * w - 1) *
        (∏ k ∈ Finset.range n, Complex.Gamma (w + (k : ℂ) / n)) * (((gm n 1 : ℝ) : ℂ))⁻¹) := by
    have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hU.mem_nhds hz] with w hw
    exact cplx_mult hn hw
  have hL := (logDeriv_congr_nhds hev).eq_of_nhds
  -- left side
  have hnz : 0 < ((n : ℂ) * z).re := by
    simp [Complex.mul_re]
    positivity
  have hdL : logDeriv (fun w : ℂ => Complex.Gamma ((n : ℂ) * w)) z
      = Complex.digamma ((n : ℂ) * z) * n := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => (n : ℂ) * w) (x := z)
      (Complex.differentiableAt_Gamma _ (re_pos_ne_neg_nat hnz))
      (differentiableAt_id.const_mul _)
    simp only [Function.comp_def] at this
    rw [this, deriv_const_mul_field', deriv_id'']
    show logDeriv Complex.Gamma ((n : ℂ) * z) * ((n : ℂ) * 1) = _
    rw [mul_one]
    rfl
  -- right side
  have hA : HasDerivAt (fun w : ℂ => (n : ℂ) ^ ((n : ℂ) * w - 1))
      ((n : ℂ) ^ ((n : ℂ) * z - 1) * Complex.log n * n) z := by
    have h0 : HasDerivAt (fun w : ℂ => (n : ℂ) * w - 1) (n : ℂ) z := by
      simpa using ((hasDerivAt_id z).const_mul (n : ℂ)).sub_const 1
    exact h0.const_cpow (Or.inl hnc)
  have hAne : (n : ℂ) ^ ((n : ℂ) * z - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  have hdA : logDeriv (fun w : ℂ => (n : ℂ) ^ ((n : ℂ) * w - 1)) z = Complex.log n * n := by
    rw [logDeriv_apply, hA.deriv]
    field_simp
  have hGk : ∀ k ∈ Finset.range n, Complex.Gamma (z + (k : ℂ) / n) ≠ 0 := by
    intro k _
    exact Complex.Gamma_ne_zero_of_re_pos (hkre z hz k)
  have hDk : ∀ k ∈ Finset.range n,
      DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + (k : ℂ) / n)) z := by
    intro k _
    have := (Complex.differentiableAt_Gamma _ (re_pos_ne_neg_nat (hkre z hz k)))
    exact this.comp z (differentiableAt_id.add_const _)
  have hdP : logDeriv (fun w : ℂ => ∏ k ∈ Finset.range n, Complex.Gamma (w + (k : ℂ) / n)) z
      = ∑ k ∈ Finset.range n, Complex.digamma (z + (k : ℂ) / n) := by
    rw [logDeriv_prod hGk hDk]
    apply Finset.sum_congr rfl
    intro k _
    have := logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => w + (k : ℂ) / n) (x := z)
      (Complex.differentiableAt_Gamma _ (re_pos_ne_neg_nat (hkre z hz k)))
      (differentiableAt_id.add_const _)
    simp only [Function.comp_def] at this
    rw [this, deriv_add_const, deriv_id'', mul_one]
    rfl
  have hR : logDeriv (fun w : ℂ => (n : ℂ) ^ ((n : ℂ) * w - 1) *
        (∏ k ∈ Finset.range n, Complex.Gamma (w + (k : ℂ) / n)) * (((gm n 1 : ℝ) : ℂ))⁻¹) z
      = Complex.log n * n + ∑ k ∈ Finset.range n, Complex.digamma (z + (k : ℂ) / n) := by
    rw [logDeriv_mul_const _ _ hc]
    rw [logDeriv_mul (f := fun w : ℂ => (n : ℂ) ^ ((n : ℂ) * w - 1))
      (g := fun w : ℂ => ∏ k ∈ Finset.range n, Complex.Gamma (w + (k : ℂ) / n)) z hAne
      (Finset.prod_ne_zero_iff.mpr hGk) hA.differentiableAt
      (DifferentiableAt.fun_finsetProd hDk)]
    rw [hdA, hdP]
  rw [hdL, hR] at hL
  rw [Complex.natCast_log]
  linear_combination -hL

end P2MDigammaMul

theorem solution (z : Complex) (hz : 0 < z.re) :
    Complex.digamma z + Complex.digamma (z + (1 : Complex) / 3) +
      Complex.digamma (z + (2 : Complex) / 3) =
        3 * Complex.digamma (3 * z) - 3 * (Real.log 3 : Complex) := by
  have h := P2MDigammaMul.mult_formula 3 (by norm_num) z hz
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_div, add_zero] at h
  exact h
