-- Prove2me | solution 2 for ErlerGross.integral_cosh_div_cosh
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T19:37:31.430002+00:00
-- url     : https://prove2.me/submissions/a15e9c03-2f7e-4a1c-aa4b-cac31d2b94f3

import Mathlib
import Definitions.Def_ErlerGross_defs

set_option autoImplicit false

open Real Filter Topology MeasureTheory Set

theorem e967_re_mul (c : ℂ) (x : ℝ) : (c * (x : ℂ)).re = c.re * x := by simp

theorem e967_norm_cosh_le (w : ℂ) :
    ‖Complex.cosh w‖ ≤ (Real.exp w.re + Real.exp (-w.re)) / 2 := by
  have h2 : Complex.cosh w = (Complex.exp w + Complex.exp (-w)) / 2 := by
    rw [← Complex.two_cosh]; ring
  rw [h2, norm_div]
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  gcongr
  calc ‖Complex.exp w + Complex.exp (-w)‖ ≤ ‖Complex.exp w‖ + ‖Complex.exp (-w)‖ :=
        norm_add_le _ _
    _ = Real.exp w.re + Real.exp (-w.re) := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

theorem e967_norm_cosh_ge (w : ℂ) :
    (Real.exp w.re - Real.exp (-w.re)) / 2 ≤ ‖Complex.cosh w‖ := by
  have h2 : Complex.cosh w = (Complex.exp w + Complex.exp (-w)) / 2 := by
    rw [← Complex.two_cosh]; ring
  rw [h2, norm_div]
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  gcongr
  have := norm_sub_le (Complex.exp w + Complex.exp (-w)) (Complex.exp (-w))
  rw [add_sub_cancel_right, Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at this
  linarith

theorem e967_cosh_ne (b : ℂ) (hb : 0 < b.re) (x : ℝ) (hx : 0 ≤ x) :
    Complex.cosh (b * x) ≠ 0 := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · intro h0
    have := e967_norm_cosh_ge (b * x)
    rw [h0, norm_zero, e967_re_mul] at this
    have : Real.exp (-(b.re * x)) < Real.exp (b.re * x) := Real.exp_lt_exp.mpr (by nlinarith)
    linarith

theorem e967_integrable (a b : ℂ) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Ioi 0) := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  have hcont : ContinuousOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Ici 0) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact e967_cosh_ne b hb x hx
  have h1 : IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Ioc 0 1) :=
    ((hcont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Ioi 1) := by
    set δ := b.re - |a.re| with hδ
    have hδpos : 0 < δ := by linarith
    set c := 1 - Real.exp (-2 * b.re) with hc
    have hcpos : 0 < c := by
      have : Real.exp (-2 * b.re) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hg : IntegrableOn (fun x : ℝ => (2 / c) * Real.exp (-δ * x)) (Ioi 1) :=
      (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 1).const_mul (2 / c)
    refine hg.mono' ((hcont.mono (Ioi_subset_Ici zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    rw [norm_div]
    have hA : ‖Complex.cosh (a * x)‖ ≤ Real.exp (|a.re| * x) := by
      refine (e967_norm_cosh_le _).trans ?_
      rw [e967_re_mul]
      have e1 : Real.exp (a.re * x) ≤ Real.exp (|a.re| * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self _) hx0)
      have e2 : Real.exp (-(a.re * x)) ≤ Real.exp (|a.re| * x) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right (neg_abs_le a.re) hx0
        linarith
      linarith
    have hB : Real.exp (b.re * x) * c / 2 ≤ ‖Complex.cosh (b * x)‖ := by
      refine le_trans ?_ (e967_norm_cosh_ge _)
      rw [e967_re_mul]
      have : Real.exp (-(b.re * x)) ≤ Real.exp (b.re * x) * Real.exp (-2 * b.re) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      have e3 : Real.exp (b.re * x) * c / 2 =
          (Real.exp (b.re * x) - Real.exp (b.re * x) * Real.exp (-2 * b.re)) / 2 := by
        rw [hc]; ring
      rw [e3]
      linarith
    have hBpos : 0 < Real.exp (b.re * x) * c / 2 := by positivity
    calc ‖Complex.cosh (a * x)‖ / ‖Complex.cosh (b * x)‖
        ≤ Real.exp (|a.re| * x) / (Real.exp (b.re * x) * c / 2) :=
          div_le_div₀ (by positivity) hA hBpos hB
      _ = (2 / c) * Real.exp (-δ * x) := by
          have : Real.exp (|a.re| * x) = Real.exp (-δ * x) * Real.exp (b.re * x) := by
            rw [← Real.exp_add]; congr 1; rw [hδ]; ring
          rw [this]
          field_simp
  have : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [this]
  exact h1.union h2

theorem e967_expand (a b : ℂ) (x : ℝ) (hx : Complex.cosh (b * x) ≠ 0) (N : ℕ) :
    Complex.cosh (a * x) / Complex.cosh (b * x) =
      ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
          (Complex.exp (-((2 * (k : ℂ) + 1) * b - a) * x) +
            Complex.exp (-((2 * (k : ℂ) + 1) * b + a) * x)) +
        (-1 : ℂ) ^ N * (Complex.exp (-(2 * (N : ℂ) * b) * x) *
          (Complex.cosh (a * x) / Complex.cosh (b * x))) := by
  set H := Complex.cosh (a * x) / Complex.cosh (b * x) with hHdef
  have hH0 : H * Complex.cosh (b * x) = Complex.cosh (a * x) := div_mul_cancel₀ _ hx
  have hH : H * (Complex.exp (b * x) + Complex.exp (-(b * x))) =
      Complex.exp (a * x) + Complex.exp (-(a * x)) := by
    rw [← Complex.two_cosh, ← Complex.two_cosh, ← hH0]
    ring
  have hBE : Complex.exp (b * x) * Complex.exp (-(b * x)) = 1 := by
    rw [← Complex.exp_add]; simp
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have e1 : Complex.exp (-((2 * (N : ℂ) + 1) * b - a) * x) =
        Complex.exp (-(2 * (N : ℂ) * b) * x) * Complex.exp (-(b * x)) * Complex.exp (a * x) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have e2 : Complex.exp (-((2 * (N : ℂ) + 1) * b + a) * x) =
        Complex.exp (-(2 * (N : ℂ) * b) * x) * Complex.exp (-(b * x)) *
          Complex.exp (-(a * x)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have e3 : Complex.exp (-(2 * ((N + 1 : ℕ) : ℂ) * b) * x) =
        Complex.exp (-(2 * (N : ℂ) * b) * x) * Complex.exp (-(b * x)) *
          Complex.exp (-(b * x)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, e3]
    conv_lhs => rw [ih]
    linear_combination ((-1 : ℂ) ^ N * Complex.exp (-(2 * (N : ℂ) * b) * x) *
        Complex.exp (-(b * x))) * hH +
      (-((-1 : ℂ) ^ N * Complex.exp (-(2 * (N : ℂ) * b) * x) * H)) * hBE

theorem e967_term (a b : ℂ) (hab : |a.re| < b.re) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (-1 : ℂ) ^ k *
          (Complex.exp (-((2 * (k : ℂ) + 1) * b - a) * x) +
            Complex.exp (-((2 * (k : ℂ) + 1) * b + a) * x))) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), (-1 : ℂ) ^ k *
          (Complex.exp (-((2 * (k : ℂ) + 1) * b - a) * x) +
            Complex.exp (-((2 * (k : ℂ) + 1) * b + a) * x)) =
      (-1 : ℂ) ^ k * (1 / ((2 * (k : ℂ) + 1) * b - a) + 1 / ((2 * (k : ℂ) + 1) * b + a)) := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  have hk : (1 : ℝ) ≤ 2 * k + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hkb : b.re ≤ (2 * k + 1) * b.re := by nlinarith
  have hre : ((2 * (k : ℂ) + 1) * b).re = (2 * k + 1) * b.re := by simp [Complex.mul_re]
  have h1 : (-((2 * (k : ℂ) + 1) * b - a)).re < 0 := by
    rw [Complex.neg_re, Complex.sub_re, hre]
    linarith [le_abs_self a.re]
  have h2 : (-((2 * (k : ℂ) + 1) * b + a)).re < 0 := by
    rw [Complex.neg_re, Complex.add_re, hre]
    linarith [neg_abs_le a.re]
  have i1 := integrableOn_exp_mul_complex_Ioi h1 0
  have i2 := integrableOn_exp_mul_complex_Ioi h2 0
  refine ⟨(i1.add i2).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add i1 i2, integral_exp_mul_complex_Ioi h1,
    integral_exp_mul_complex_Ioi h2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [neg_div_neg_eq, neg_div_neg_eq]

theorem e967_tendsto_inv (x : ℂ) : Tendsto (fun M : ℕ => 1 / (x + M)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [one_div, norm_inv]
  apply Tendsto.inv_tendsto_atTop
  have h1 : Tendsto (fun M : ℕ => (M : ℝ) + -‖x‖) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono (fun M => ?_) h1
  have := norm_sub_le (x + (M : ℂ)) x
  rw [add_sub_cancel_left, Complex.norm_natCast] at this
  linarith

theorem e967_mem (a b : ℂ) (hab : |a.re| < b.re) (p : ℤ)
    (hpodd : ∀ n : ℤ, p - 4 * n ≠ 0) :
    ((p : ℂ) * b - a) / (4 * b) ∈ Complex.integerComplement := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  have hb0 : b ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hb; exact lt_irrefl _ hb
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  rw [eq_div_iff (by simpa using hb0 : (4 : ℂ) * b ≠ 0)] at hn
  have ha : a = ((p : ℂ) - 4 * (n : ℂ)) * b := by linear_combination hn
  have hre : a.re = ((p : ℝ) - 4 * (n : ℝ)) * b.re := by rw [ha]; simp [Complex.mul_re]
  have h1 : (1 : ℝ) ≤ |(p : ℝ) - 4 * (n : ℝ)| := by
    have : (1 : ℤ) ≤ |p - 4 * n| := Int.one_le_abs (hpodd n)
    exact_mod_cast this
  have : |a.re| = |(p : ℝ) - 4 * (n : ℝ)| * b.re := by rw [hre, abs_mul, abs_of_pos hb]
  nlinarith [mul_le_mul_of_nonneg_right h1 hb.le]

theorem e967_pf (a b : ℂ) (hab : |a.re| < b.re) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.range (2 * M), (-1 : ℂ) ^ k *
        (1 / ((2 * (k : ℂ) + 1) * b - a) + 1 / ((2 * (k : ℂ) + 1) * b + a))) atTop
      (𝓝 ((π : ℂ) / (2 * b) * (1 / Complex.cos (π * a / (2 * b))))) := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  have hb0 : b ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hb; exact lt_irrefl _ hb
  obtain ⟨x₁, hx₁d⟩ : ∃ x₁ : ℂ, x₁ = (((1 : ℤ) : ℂ) * b - a) / (4 * b) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂d⟩ : ∃ x₂ : ℂ, x₂ = (((3 : ℤ) : ℂ) * b - a) / (4 * b) := ⟨_, rfl⟩
  have hx₁ : x₁ ∈ Complex.integerComplement := by
    rw [hx₁d]; exact e967_mem a b hab 1 (fun n => by omega)
  have hx₂ : x₂ ∈ Complex.integerComplement := by
    rw [hx₂d]; exact e967_mem a b hab 3 (fun n => by omega)
  -- per-step identity
  have hstep : ∀ M : ℕ,
      (-1 : ℂ) ^ (2 * M) * (1 / ((2 * ((2 * M : ℕ) : ℂ) + 1) * b - a) +
          1 / ((2 * ((2 * M : ℕ) : ℂ) + 1) * b + a)) +
        (-1 : ℂ) ^ (2 * M + 1) * (1 / ((2 * ((2 * M + 1 : ℕ) : ℂ) + 1) * b - a) +
          1 / ((2 * ((2 * M + 1 : ℕ) : ℂ) + 1) * b + a)) =
      1 / (4 * b) * (cotTerm x₁ M - cotTerm x₂ M + (1 / (x₁ + M) - 1 / (x₁ + ((M + 1 : ℕ) : ℂ))) -
        (1 / (x₂ + M) - 1 / (x₂ + ((M + 1 : ℕ) : ℂ)))) := by
    intro M
    have p1 : (-1 : ℂ) ^ (2 * M) = 1 := by rw [pow_mul]; simp
    have p2 : (-1 : ℂ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; simp
    have r1 : 1 / (x₁ + M) = 4 * b * (1 / ((4 * (M : ℂ) + 1) * b - a)) := by
      rw [show x₁ + M = ((4 * (M : ℂ) + 1) * b - a) / (4 * b) by
        rw [hx₁d]; field_simp; push_cast; ring, one_div_div]
      ring
    have r2 : 1 / (x₂ + M) = 4 * b * (1 / ((4 * (M : ℂ) + 3) * b - a)) := by
      rw [show x₂ + M = ((4 * (M : ℂ) + 3) * b - a) / (4 * b) by
        rw [hx₂d]; field_simp; push_cast; ring, one_div_div]
      ring
    have r3 : 1 / (x₂ - ((M : ℂ) + 1)) = -(4 * b) * (1 / ((4 * (M : ℂ) + 1) * b + a)) := by
      rw [show x₂ - ((M : ℂ) + 1) = ((4 * (M : ℂ) + 1) * b + a) / (-(4 * b)) by
        rw [hx₂d]; field_simp; push_cast; ring, one_div_div]
      ring
    have r4 : 1 / (x₁ - ((M : ℂ) + 1)) = -(4 * b) * (1 / ((4 * (M : ℂ) + 3) * b + a)) := by
      rw [show x₁ - ((M : ℂ) + 1) = ((4 * (M : ℂ) + 3) * b + a) / (-(4 * b)) by
        rw [hx₁d]; field_simp; push_cast; ring, one_div_div]
      ring
    have h4b : 1 / (4 * b) * (4 * b) = 1 := by field_simp
    simp only [cotTerm]
    push_cast
    rw [p1, p2, r1, r2, r3, r4]
    have c1 : (2 * (2 * (M : ℂ)) + 1) * b - a = (4 * (M : ℂ) + 1) * b - a := by ring
    have c2 : (2 * (2 * (M : ℂ)) + 1) * b + a = (4 * (M : ℂ) + 1) * b + a := by ring
    have c3 : (2 * (2 * (M : ℂ) + 1) + 1) * b - a = (4 * (M : ℂ) + 3) * b - a := by ring
    have c4 : (2 * (2 * (M : ℂ) + 1) + 1) * b + a = (4 * (M : ℂ) + 3) * b + a := by ring
    rw [c1, c2, c3, c4]
    linear_combination (-(1 / ((4 * (M : ℂ) + 1) * b - a) + 1 / ((4 * (M : ℂ) + 1) * b + a) -
      1 / ((4 * (M : ℂ) + 3) * b - a) - 1 / ((4 * (M : ℂ) + 3) * b + a))) * h4b
  have hS2M : ∀ M : ℕ, ∑ k ∈ Finset.range (2 * M), (-1 : ℂ) ^ k *
        (1 / ((2 * (k : ℂ) + 1) * b - a) + 1 / ((2 * (k : ℂ) + 1) * b + a)) =
      1 / (4 * b) * ((∑ j ∈ Finset.range M, cotTerm x₁ j - ∑ j ∈ Finset.range M, cotTerm x₂ j) +
        (1 / x₁ - 1 / (x₁ + M)) - (1 / x₂ - 1 / (x₂ + M))) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, add_assoc, hstep M, Finset.sum_range_succ, Finset.sum_range_succ]
      ring
  have hcot : (π : ℂ) * Complex.cot (π * x₁) - π * Complex.cot (π * x₂) =
      2 * π / Complex.cos (π * a / (2 * b)) := by
    set u := (π : ℂ) * x₁ with hu
    have hu2 : (π : ℂ) * x₂ = u + π / 2 := by
      rw [hu, hx₁d, hx₂d]; field_simp; push_cast; ring
    have hθ : (π : ℂ) * a / (2 * b) = π / 2 - 2 * u := by
      rw [hu, hx₁d]; field_simp; push_cast; ring
    have hs : Complex.sin u ≠ 0 := sin_pi_mul_ne_zero hx₁
    have hc : Complex.cos u ≠ 0 := by
      have := sin_pi_mul_ne_zero hx₂
      rwa [hu2, Complex.sin_add_pi_div_two] at this
    rw [hu2, hθ, Complex.cos_pi_div_two_sub, Complex.sin_two_mul, Complex.cot_eq_cos_div_sin,
      Complex.cot_eq_cos_div_sin, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two]
    field_simp
    linear_combination Complex.sin_sq_add_cos_sq u
  have hL1 := tendsto_logDeriv_euler_cot_sub hx₁
  have hL2 := tendsto_logDeriv_euler_cot_sub hx₂
  have hlim := ((((hL1.sub hL2).add ((tendsto_const_nhds (x := 1 / x₁)).sub
    (e967_tendsto_inv x₁))).sub ((tendsto_const_nhds (x := 1 / x₂)).sub
    (e967_tendsto_inv x₂))).const_mul (1 / (4 * b)))
  have hval : 1 / (4 * b) * ((π * Complex.cot (π * x₁) - 1 / x₁ - (π * Complex.cot (π * x₂) - 1 / x₂))
      + (1 / x₁ - 0) - (1 / x₂ - 0)) =
      (π : ℂ) / (2 * b) * (1 / Complex.cos (π * a / (2 * b))) := by
    rw [show (π * Complex.cot (π * x₁) - 1 / x₁ - (π * Complex.cot (π * x₂) - 1 / x₂))
      + (1 / x₁ - 0) - (1 / x₂ - 0) = (π : ℂ) * Complex.cot (π * x₁) - π * Complex.cot (π * x₂)
      by ring, hcot]
    ring
  rw [hval] at hlim
  refine hlim.congr (fun M => ?_)
  rw [hS2M M]

open Real Filter Topology MeasureTheory ErlerGross in
theorem solution (a b : ℂ) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), Complex.cosh (a * x) / Complex.cosh (b * x) =
        (π : ℂ) / (2 * b) * (1 / Complex.cos (π * a / (2 * b))) := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  have hint := e967_integrable a b hab
  refine ⟨hint, ?_⟩
  obtain ⟨S, hSd⟩ : ∃ S : ℕ → ℂ, S = fun N => ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
      (1 / ((2 * (k : ℂ) + 1) * b - a) + 1 / ((2 * (k : ℂ) + 1) * b + a)) := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : ℕ → ℂ, R = fun N : ℕ => ∫ x in Set.Ioi (0 : ℝ),
      Complex.exp (-(2 * (N : ℂ) * b) * x) * (Complex.cosh (a * x) / Complex.cosh (b * x)) :=
    ⟨_, rfl⟩
  have hbound : ∀ N : ℕ, ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖Complex.exp (-(2 * (N : ℂ) * b) * x) * (Complex.cosh (a * x) / Complex.cosh (b * x))‖ ≤
        ‖Complex.cosh (a * x) / Complex.cosh (b * x)‖ := by
    intro N x hx
    have hx' : (0 : ℝ) < x := hx
    rw [norm_mul]
    have : ‖Complex.exp (-(2 * (N : ℂ) * b) * x)‖ ≤ 1 := by
      rw [Complex.norm_exp, e967_re_mul]
      apply Real.exp_le_one_iff.mpr
      have hre : (-(2 * (N : ℂ) * b)).re = -(2 * N * b.re) := by simp [Complex.mul_re]
      rw [hre]
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : 0 ≤ 2 * (N : ℝ) * b.re := by positivity
      nlinarith
    calc _ ≤ 1 * ‖Complex.cosh (a * x) / Complex.cosh (b * x)‖ := by gcongr
      _ = _ := one_mul _
  have hFint : ∀ N : ℕ, IntegrableOn (fun x : ℝ => Complex.exp (-(2 * (N : ℂ) * b) * x) *
      (Complex.cosh (a * x) / Complex.cosh (b * x))) (Set.Ioi 0) := by
    intro N
    refine hint.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      hint.aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound N))
  have hId : ∀ N : ℕ, (∫ x in Set.Ioi (0 : ℝ), Complex.cosh (a * x) / Complex.cosh (b * x)) =
      S N + (-1 : ℂ) ^ N * R N := by
    intro N
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => e967_expand a b x (e967_cosh_ne b hb x (le_of_lt hx)) N)]
    rw [integral_add (integrable_finsetSum _ (fun k _ => (e967_term a b hab k).1))
      ((hFint N).const_mul _)]
    rw [MeasureTheory.integral_finsetSum _ (fun k _ => (e967_term a b hab k).1),
      integral_const_mul, hSd, hRd]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => (e967_term a b hab k).2)
  have hR : Tendsto R atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := fun (N : ℕ) (x : ℝ) => Complex.exp (-(2 * (N : ℂ) * b) * x) *
        (Complex.cosh (a * x) / Complex.cosh (b * x)))
      (f := fun _ => (0 : ℂ)) (fun x => ‖Complex.cosh (a * x) / Complex.cosh (b * x)‖)
      (fun N => (hFint N).aestronglyMeasurable) hint.norm
      (fun N => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound N))) ?_
    · rw [hRd]; simpa using h
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx' : (0 : ℝ) < x := hx
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : ∀ N : ℕ, ‖Complex.exp (-(2 * (N : ℂ) * b) * x) *
          (Complex.cosh (a * x) / Complex.cosh (b * x))‖ =
          (Real.exp (-2 * b.re * x)) ^ N * ‖Complex.cosh (a * x) / Complex.cosh (b * x)‖ := by
        intro N
        rw [norm_mul, Complex.norm_exp, e967_re_mul, ← Real.exp_nat_mul]
        have hre : (-(2 * (N : ℂ) * b)).re = -(2 * N * b.re) := by simp [Complex.mul_re]
        rw [hre]
        congr 2
        ring
      simp_rw [heq]
      have hq : Real.exp (-2 * b.re * x) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq).mul_const
        ‖Complex.cosh (a * x) / Complex.cosh (b * x)‖
  have hS : Tendsto S atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), Complex.cosh (a * x) / Complex.cosh (b * x))) := by
    have h0 : Tendsto (fun N : ℕ => (-1 : ℂ) ^ N * R N) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [norm_mul, norm_pow] using (tendsto_zero_iff_norm_tendsto_zero.mp hR)
    have := (tendsto_const_nhds
      (x := ∫ x in Set.Ioi (0 : ℝ), Complex.cosh (a * x) / Complex.cosh (b * x))).sub h0
    rw [sub_zero] at this
    refine this.congr (fun N => ?_)
    rw [hId N]; ring
  have htwo : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun c => ⟨c, fun M hM => by omega⟩)
  have hS2 := e967_pf a b hab
  exact tendsto_nhds_unique (hS.comp htwo) (by rw [hSd]; exact hS2)
