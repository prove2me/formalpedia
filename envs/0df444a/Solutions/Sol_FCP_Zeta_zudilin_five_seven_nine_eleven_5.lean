-- Prove2me | solution 5 for FCP.Zeta.zudilin_five_seven_nine_eleven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T10:02:24.415373+00:00
-- url     : https://prove2.me/submissions/1c8ce147-2d1a-4348-a657-8c7539e50a60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZudilinZeta_params13_contour_formula
import Mathlib
import Theorems.Thm_ZudilinZeta_zudilin_lcm_asymptotics
import Theorems.Thm_ZudilinZeta_zudilin_phi_log_growth_fixed
import Theorems.Thm_ZudilinZeta_zudilin_phi_tail_integral_eq
import Definitions.Def_ZudilinZetaAsymp
import Theorems.Thm_ZudilinZeta_zudilin_small_values_criterion
import Theorems.Thm_ZudilinZeta_params13_kernel_saddle_limit_nonzero
import Theorems.Thm_ZudilinZeta_exists_saddle_root_params13
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_bounds
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C1_upper_bound
import Theorems.Thm_ZudilinZeta_zetaR_eq_riemannZeta

-- Component: missions.zudilin.ComplexExponentialOscillation
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta

lemma re_rotation_mul (u : ℝ) (c : ℂ) :
    (Complex.exp ((u : ℂ) * I) * c).re = ‖c‖ * Real.cos (u + Complex.arg c) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]
  rw [mul_left_comm, ← Complex.exp_add]
  have he : (u : ℂ) * I + (Complex.arg c : ℂ) * I = ((u + Complex.arg c : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he]
  simp [Complex.mul_re, Complex.exp_re]

lemma tendsto_re_rotations_of_complex_limit {v : ℕ → ℂ} {c : ℂ}
    (hv : Tendsto v atTop (𝓝 c)) (hc : c ≠ 0) (θ : ℝ) :
    Tendsto (fun n : ℕ =>
      (Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * v n).re / ‖c‖ -
        Real.cos ((n : ℝ) * θ + Complex.arg c)) atTop (𝓝 0) := by
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have he (n : ℕ) :
      (Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * v n).re / ‖c‖ -
        Real.cos ((n : ℝ) * θ + Complex.arg c) =
      (Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * (v n - c)).re / ‖c‖ := by
    rw [mul_sub, Complex.sub_re, sub_div, re_rotation_mul _ c, mul_div_cancel_left₀ _ hcp.ne']
  have hb (n : ℕ) :
      |(Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * (I : ℂ)) * (v n - c)).re / ‖c‖| ≤
        ‖v n - c‖ / ‖c‖ := by
    rw [abs_div, abs_of_pos hcp]
    apply div_le_div_of_nonneg_right _ hcp.le
    have hh := Complex.abs_re_le_norm
      (Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * (v n - c))
    simpa [norm_mul, Complex.norm_exp] using hh
  have hzero : Tendsto (fun n : ℕ => ‖v n - c‖ / ‖c‖) atTop (𝓝 0) := by
    simpa using (hv.sub_const c).norm.div_const ‖c‖
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs, he]
  exact squeeze_zero (fun _ => abs_nonneg _) hb hzero

lemma tendsto_abs_re_rotations_of_complex_limit {v : ℕ → ℂ} {c : ℂ}
    (hv : Tendsto v atTop (𝓝 c)) (hc : c ≠ 0) (θ : ℝ) :
    Tendsto (fun n : ℕ =>
      |(Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * v n).re| / ‖c‖ -
        |Real.cos ((n : ℝ) * θ + Complex.arg c)|) atTop (𝓝 0) := by
  have h := tendsto_re_rotations_of_complex_limit hv hc θ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb (n : ℕ) :
      ‖|(Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * v n).re| / ‖c‖ -
          |Real.cos ((n : ℝ) * θ + Complex.arg c)|‖ ≤
      ‖(Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * v n).re / ‖c‖ -
          Real.cos ((n : ℝ) * θ + Complex.arg c)‖ := by
    have hh := abs_abs_sub_abs_le_abs_sub
      ((Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * I) * v n).re / ‖c‖)
      (Real.cos ((n : ℝ) * θ + Complex.arg c))
    simpa only [abs_div, abs_norm, Real.norm_eq_abs] using hh
  exact squeeze_zero (fun _ => norm_nonneg _) hb (by simpa using h.norm)

end ZudilinZeta
end
end

-- Component: missions.zudilin.ArithmeticNormalizer
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace ZudilinZeta

noncomputable def arithmeticNormalizer (P : Params) (n : ℕ) : ℝ :=
  ((D (m P 1 * n) : ℝ)^P.r *
    ∏ j ∈ Finset.Icc 2 (P.q-P.r), (D (m P j * n) : ℝ)) / (Phi P n : ℝ)

private lemma d_pos (N : ℕ) : 0 < (D N : ℝ) := by
  have h : D N ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro k hk
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
  exact_mod_cast Nat.pos_of_ne_zero h

private lemma phi_pos (P : Params) (n : ℕ) : 0 < (Phi P n : ℝ) := by
  have h : 0 < Phi P n := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Finset.mem_filter.mp hp).2.1.pos _
  exact_mod_cast h

lemma arithmeticNormalizer_log_tendsto (P : Params) :
    Tendsto (fun n : ℕ => Real.log (arithmeticNormalizer P n) / (n : ℝ))
      atTop (𝓝 (C1 P)) := by
  unfold arithmeticNormalizer
  have hq : 1 ≤ P.q - P.r := by have := P.q_ge; omega
  have hfirst := (zudilin_lcm_asymptotics P 1 le_rfl hq).const_mul (P.r : ℝ)
  have hsum : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.Icc 2 (P.q - P.r), Real.log (D (m P j * n) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ j ∈ Finset.Icc 2 (P.q - P.r), (m P j : ℝ))) := by
    apply tendsto_finsetSum
    intro j hj
    exact zudilin_lcm_asymptotics P j (by have := (Finset.mem_Icc.mp hj).1; omega)
      (Finset.mem_Icc.mp hj).2
  have hphi := zudilin_phi_log_growth_fixed P
  rw [zudilin_phi_tail_integral_eq P] at hphi
  unfold C1
  convert (hfirst.add hsum).sub hphi using 1
  funext n
  have hd : (D (m P 1 * n) : ℝ) ≠ 0 := (d_pos _).ne'
  have hp : (∏ j ∈ Finset.Icc 2 (P.q - P.r), (D (m P j * n) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => (d_pos _).ne')
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hd) hp) (phi_pos P n).ne',
    Real.log_mul (pow_ne_zero _ hd) hp, Real.log_pow,
    Real.log_prod (fun j _ => (d_pos (m P j * n)).ne'), sub_div, add_div,
    Finset.sum_div]
  ring

lemma arithmeticNormalizer_pos (P : Params) (n : ℕ) : 0<arithmeticNormalizer P n :=
  div_pos (mul_pos (pow_pos (d_pos _) _) (Finset.prod_pos (fun j _ => d_pos _)))
    (phi_pos P n)

lemma Lambda_eq_arithmeticNormalizer_mul (P : Params) (n : ℕ) :
    Lambda P n=arithmeticNormalizer P n*F P n := rfl

end ZudilinZeta
end

-- Component: missions.zudilin.OscillatoryNonvanishing
section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ZudilinZeta

lemma sine_le_adjacent_cosines (θ t : ℝ) :
    |Real.sin θ|≤ |Real.cos t|+|Real.cos (t+θ)| := by
  have he : Real.sin θ=Real.sin (t+θ)*Real.cos t-Real.cos (t+θ)*Real.sin t := by
    rw [← Real.sin_sub]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ |Real.sin (t+θ)*Real.cos t|+|Real.cos (t+θ)*Real.sin t| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Real.sin (t+θ)*Real.cos t) (-(Real.cos (t+θ)*Real.sin t))
    _ ≤ |Real.cos t|+|Real.cos (t+θ)| := by
      rw [abs_mul, abs_mul]
      have h1 := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (t+θ))
        (abs_nonneg (Real.cos t))
      have h2 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t)
        (abs_nonneg (Real.cos (t+θ)))
      linarith only [h1, h2]

lemma frequently_cosine_bounded_away_zero (θ c : ℝ) (hθ : Real.sin θ≠0) :
    ∃ ε : ℝ, 0<ε ∧ ∃ᶠ n : ℕ in Filter.atTop, ε≤ |Real.cos ((n : ℝ)*θ+c)| := by
  have hs : 0 < |Real.sin θ| := abs_pos.mpr hθ
  refine ⟨|Real.sin θ|/2, by positivity, Filter.frequently_atTop.mpr ?_⟩
  intro N
  by_cases hN : |Real.sin θ|/2≤ |Real.cos ((N : ℝ)*θ+c)|
  · exact ⟨N, le_rfl, hN⟩
  · refine ⟨N+1, by omega, ?_⟩
    have hh := sine_le_adjacent_cosines θ ((N : ℝ)*θ+c)
    rw [show ((N+1 : ℕ) : ℝ)*θ+c=(N : ℝ)*θ+c+θ by push_cast; ring]
    linarith only [hh, hN]

lemma sine_ne_zero_of_phase_nonresonant (θ : ℝ)
    (hθ : ∀ k : ℤ, θ≠(k : ℝ)*Real.pi) : Real.sin θ≠0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  exact hθ k hk.symm

lemma frequently_ne_zero_of_cosine_asymptotic (f u : ℕ → ℝ) (θ c : ℝ)
    (hθ : Real.sin θ≠0)
    (h : Tendsto (fun n : ℕ => f n/u n-Real.cos ((n : ℝ)*θ+c)) atTop (𝓝 0)) :
    ∃ᶠ n : ℕ in atTop, f n≠0 := by
  obtain ⟨ε, hε, hfreq⟩ := frequently_cosine_bounded_away_zero θ c hθ
  have herr : ∀ᶠ n : ℕ in atTop,
      |f n/u n-Real.cos ((n : ℝ)*θ+c)|<ε/2 := by
    simpa only [Real.norm_eq_abs, norm_zero] using
      h.norm.eventually_lt_const (show ‖(0 : ℝ)‖<ε/2 by simp; positivity)
  apply (hfreq.and_eventually herr).mono
  rintro n ⟨hcos, herror⟩ hn
  simp only [hn, zero_div, zero_sub, abs_neg] at herror
  linarith only [hcos, herror, hε]

lemma eventually_cosine_asymptotic_bounded (f u : ℕ → ℝ) (θ c : ℝ)
    (h : Tendsto (fun n : ℕ => f n/u n-Real.cos ((n : ℝ)*θ+c)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, |f n/u n|≤2 := by
  have herr : ∀ᶠ n : ℕ in atTop,
      |f n/u n-Real.cos ((n : ℝ)*θ+c)|<1 := by
    simpa only [Real.norm_eq_abs, norm_zero] using
      h.norm.eventually_lt_const (by norm_num : ‖(0 : ℝ)‖<1)
  filter_upwards [herr] with n hn
  have hh := abs_add_le (f n/u n-Real.cos ((n : ℝ)*θ+c)) (Real.cos ((n : ℝ)*θ+c))
  rw [sub_add_cancel] at hh
  linarith only [hh, hn, Real.abs_cos_le_one ((n : ℝ)*θ+c)]

end ZudilinZeta
end

-- Component: missions.zudilin.NormalizedOscillation
section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ZudilinZeta

lemma tendsto_zero_of_negative_log_rate (v : ℕ → ℝ) (r : ℝ)
    (hv : ∀ n : ℕ, 0<n → 0<v n)
    (hlim : Tendsto (fun n : ℕ => Real.log (v n)/(n : ℝ)) atTop (𝓝 r)) (hr : r<0) :
    Tendsto v atTop (𝓝 0) := by
  have hc : r/2<0 := by linarith
  have hexp : Tendsto (fun n : ℕ => Real.exp ((r/2)*(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)
  apply squeeze_zero' ((eventually_gt_atTop 0).mono (fun n hn => (hv n hn).le)) _ hexp
  filter_upwards [hlim.eventually_lt_const (show r<r/2 by linarith),
    eventually_gt_atTop 0] with n hn hpos
  have hpos' : (0 : ℝ)<n := by exact_mod_cast hpos
  rw [← Real.exp_log (hv n hpos)]
  exact (Real.exp_lt_exp.mpr ((div_lt_iff₀ hpos').mp hn)).le

lemma tendsto_product_zero_of_log_rates (A u : ℕ → ℝ) (a r : ℝ)
    (hA : ∀ n : ℕ, 0<A n) (hu : ∀ n : ℕ, 0<n → 0<u n)
    (hAlim : Tendsto (fun n : ℕ => Real.log (A n)/(n : ℝ)) atTop (𝓝 a))
    (hulim : Tendsto (fun n : ℕ => Real.log (u n)/(n : ℝ)) atTop (𝓝 r))
    (hgap : a+r<0) : Tendsto (fun n => A n*u n) atTop (𝓝 0) := by
  apply tendsto_zero_of_negative_log_rate (fun n => A n*u n) (a+r)
    (fun n hn => mul_pos (hA n) (hu n hn)) _ hgap
  apply (hAlim.add hulim).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.log_mul (hA n).ne' (hu n hn).ne', add_div]

lemma tendsto_normalized_cosine_forms (A u f : ℕ → ℝ) (θ c : ℝ)
    (hA : ∀ n : ℕ, 0<A n) (hu : ∀ n : ℕ, 0<n → 0<u n)
    (hAu : Tendsto (fun n => A n*u n) atTop (𝓝 0))
    (hasymp : Tendsto (fun n : ℕ => f n/u n-Real.cos ((n : ℝ)*θ+c)) atTop (𝓝 0)) :
    Tendsto (fun n => A n*f n) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop, |A n*f n|≤2*(A n*u n) := by
    filter_upwards [eventually_cosine_asymptotic_bounded f u θ c hasymp,
      eventually_gt_atTop 0] with n hn hpos
    have he : A n*f n=(A n*u n)*(f n/u n) := by
      field_simp [(hu n hpos).ne']
    rw [he, abs_mul, abs_of_pos (mul_pos (hA n) (hu n hpos))]
    nlinarith only [hn, mul_pos (hA n) (hu n hpos)]
  have hzero : Tendsto (fun n => 2*(A n*u n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hAu.const_mul 2
  have habs : Tendsto (fun n => |A n*f n|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) hbound hzero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

lemma small_nonzero_products_of_cosine_asymptotic (A u f : ℕ → ℝ) (a r θ c : ℝ)
    (hA : ∀ n : ℕ, 0<A n) (hu : ∀ n : ℕ, 0<n → 0<u n)
    (hAlim : Tendsto (fun n : ℕ => Real.log (A n)/(n : ℝ)) atTop (𝓝 a))
    (hulim : Tendsto (fun n : ℕ => Real.log (u n)/(n : ℝ)) atTop (𝓝 r))
    (hgap : a+r<0) (hθ : Real.sin θ≠0)
    (hasymp : Tendsto (fun n : ℕ => f n/u n-Real.cos ((n : ℝ)*θ+c)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0<ε → ∃ n : ℕ, 0<n ∧ A n*f n≠0 ∧ |A n*f n|<ε := by
  have hAu := tendsto_product_zero_of_log_rates A u a r hA hu hAlim hulim hgap
  have hlim := tendsto_normalized_cosine_forms A u f θ c hA hu hAu hasymp
  have hfreq := frequently_ne_zero_of_cosine_asymptotic f u θ c hθ hasymp
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, |A n*f n|<ε := by
    simpa only [Real.norm_eq_abs, norm_zero] using
      hlim.norm.eventually_lt_const (by simpa only [norm_zero] using hε)
  obtain ⟨n, hnzero, hnsmall, hnpos⟩ :=
    (hfreq.and_eventually (hsmall.and (eventually_gt_atTop 0))).exists
  exact ⟨n, hnpos, mul_ne_zero (hA n).ne' hnzero, hnsmall⟩

end ZudilinZeta
end

-- Component: missions.zudilin.SaddleModelCriterion
section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ZudilinZeta

noncomputable def exponentialPowerModel (a b r : ℝ) (n : ℕ) : ℝ :=
  a*(n : ℝ)^b*Real.exp ((n : ℝ)*r)

lemma exponentialPowerModel_pos (a b r : ℝ) (ha : 0<a) (n : ℕ) (hn : 0<n) :
    0<exponentialPowerModel a b r n := by
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  exact mul_pos (mul_pos ha (Real.rpow_pos_of_pos hn' b)) (Real.exp_pos _)

lemma exponentialPowerModel_log_rate (a b r : ℝ) (ha : 0<a) :
    Tendsto (fun n : ℕ => Real.log (exponentialPowerModel a b r n)/(n : ℝ))
      atTop (𝓝 r) := by
  have hninf : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hninf
  have hconst : Tendsto (fun n : ℕ => Real.log a/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hninf
  have hlim : Tendsto
      (fun n : ℕ => Real.log a/(n : ℝ)+b*(Real.log (n : ℝ)/(n : ℝ))+r)
      atTop (𝓝 r) := by
    simpa only [mul_zero, add_zero, zero_add] using (hconst.add (hlog.const_mul b)).add_const r
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  unfold exponentialPowerModel
  rw [Real.log_mul (mul_pos ha (Real.rpow_pos_of_pos hn' b)).ne' (Real.exp_pos _).ne',
    Real.log_mul ha.ne' (Real.rpow_pos_of_pos hn' b).ne', Real.log_rpow hn' b, Real.log_exp]
  field_simp [hn'.ne'] <;> ring

lemma irrational_zeta_of_cosine_saddle_model (P : Params) (hr : P.r=3) (τ : ℂ)
    (hC : C1 P<C0 P τ) (hpi : ∀ k : ℤ, (f0 P τ).im≠(k : ℝ)*Real.pi)
    (a b c : ℝ) (ha : 0<a)
    (hasymp : Tendsto (fun n : ℕ =>
      F P n/exponentialPowerModel a b (f0 P τ).re n-
        Real.cos ((n : ℝ)*(f0 P τ).im+c)) atTop (𝓝 0)) :
    ∃ k∈Finset.Icc 1 ((P.q-P.r-2)/2), Irrational (zetaR (P.r+2*k)) := by
  have hgap : C1 P+(f0 P τ).re<0 := by
    unfold C0 at hC
    linarith only [hC]
  have hs := small_nonzero_products_of_cosine_asymptotic (arithmeticNormalizer P)
    (exponentialPowerModel a b (f0 P τ).re) (F P) (C1 P) (f0 P τ).re (f0 P τ).im c
    (arithmeticNormalizer_pos P) (exponentialPowerModel_pos a b (f0 P τ).re ha)
    (arithmeticNormalizer_log_tendsto P) (exponentialPowerModel_log_rate a b (f0 P τ).re ha)
    hgap (sine_ne_zero_of_phase_nonresonant _ hpi) hasymp
  apply zudilin_small_values_criterion P hr
  simpa only [← Lambda_eq_arithmeticNormalizer_mul] using hs

end ZudilinZeta
end

-- Component: missions.zudilin.ComplexSaddleCriterion
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta

lemma complex_normalization_reconstruction (β : ℝ) (hβ : 0 < β) (s J : ℂ) :
    J = ((Real.exp s.re / β : ℝ) : ℂ) *
      (Complex.exp ((s.im : ℂ) * I) * ((β : ℂ) * Complex.exp (-s) * J)) := by
  have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have he : (Complex.exp (s.re : ℂ) * Complex.exp ((s.im : ℂ) * I)) *
      Complex.exp (-s) = 1 := by
    rw [← Complex.exp_add, Complex.re_add_im, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc
    J = (Complex.exp (s.re : ℂ) * Complex.exp ((s.im : ℂ) * I)) * Complex.exp (-s) * J := by
      rw [he, one_mul]
    _ = _ := by rw [Complex.ofReal_div, Complex.ofReal_exp]; field_simp [hb] <;> ring

lemma small_nonzero_of_complex_saddle
    (A f β q : ℕ → ℝ) (J : ℕ → ℂ) (s c : ℂ) (B : ℝ)
    (hA : ∀ n : ℕ, 0 < A n) (hc : c ≠ 0) (hB : 0 ≤ B)
    (hphase : Real.sin s.im ≠ 0)
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < β n ∧ 0 < q n ∧ q n / β n ≤ B)
    (hlink : ∀ᶠ n : ℕ in atTop, |f n| = q n * |(J n).re|)
    (hlim : Tendsto (fun n : ℕ => (β n : ℂ) * Complex.exp (-(n : ℂ) * s) * J n)
      atTop (𝓝 c))
    (hdecay : Tendsto (fun n : ℕ => A n * Real.exp ((n : ℝ) * s.re)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ A n * f n ≠ 0 ∧ |A n * f n| < ε := by
  let W : ℕ → ℂ := fun n => (β n : ℂ) * Complex.exp (-(n : ℂ) * s) * J n
  let r : ℕ → ℝ := fun n => (Complex.exp ((((n : ℝ) * s.im : ℝ) : ℂ) * I) * W n).re
  have hrec (n : ℕ) (hb : 0 < β n) :
      J n = ((Real.exp ((n : ℝ) * s.re) / β n : ℝ) : ℂ) *
        (Complex.exp ((((n : ℝ) * s.im : ℝ) : ℂ) * I) * W n) := by
    simpa only [W, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, add_zero, neg_mul] using
      complex_normalization_reconstruction (β n) hb ((n : ℂ) * s) (J n)
  have hrot : ∃ᶠ n : ℕ in atTop, r n ≠ 0 := by
    apply frequently_ne_zero_of_cosine_asymptotic r (fun _ => ‖c‖) s.im c.arg hphase
    exact tendsto_re_rotations_of_complex_limit hlim hc s.im
  have hfreq : ∃ᶠ n : ℕ in atTop, f n ≠ 0 := by
    apply (hrot.and_eventually (hscale.and hlink)).mono
    rintro n ⟨hr, hs, hl⟩ hf
    have hJ : (J n).re = 0 := by
      rw [hf, abs_zero] at hl
      exact abs_eq_zero.mp ((mul_eq_zero.mp hl.symm).resolve_left hs.2.1.ne')
    have hh := congrArg Complex.re (hrec n hs.1)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
    change (J n).re = (Real.exp ((n : ℝ) * s.re) / β n) * r n at hh
    rw [hJ] at hh
    exact hr ((mul_eq_zero.mp hh.symm).resolve_left (div_pos (Real.exp_pos _) hs.1).ne')
  have hW : ∀ᶠ n : ℕ in atTop, ‖W n‖ ≤ ‖c‖ + 1 :=
    (hlim.norm.eventually_lt_const (by linarith : ‖c‖ < ‖c‖ + 1)).mono fun _ hn => hn.le
  have hbound : ∀ᶠ n : ℕ in atTop,
      |f n| ≤ (B * (‖c‖ + 1)) * Real.exp ((n : ℝ) * s.re) := by
    filter_upwards [hscale, hlink, hW] with n hs hl hw
    have hcoef : 0 < Real.exp ((n : ℝ) * s.re) / β n := div_pos (Real.exp_pos _) hs.1
    have hJnorm : ‖J n‖ = (Real.exp ((n : ℝ) * s.re) / β n) * ‖W n‖ := by
      rw [hrec n hs.1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoef, norm_mul]
      simp [Complex.norm_exp]
    calc
      |f n| = q n * |(J n).re| := hl
      _ ≤ q n * ‖J n‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hs.2.1.le
      _ = (q n / β n) * Real.exp ((n : ℝ) * s.re) * ‖W n‖ := by rw [hJnorm]; ring
      _ ≤ B * Real.exp ((n : ℝ) * s.re) * (‖c‖ + 1) := by
        gcongr
        exact hs.2.2
      _ = _ := by ring
  have hzero : Tendsto (fun n => A n * f n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa using hdecay.const_mul (B * (‖c‖ + 1)))
    filter_upwards [hbound] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hA n)]
    have hh := mul_le_mul_of_nonneg_left hn (hA n).le
    convert! hh using 1 <;> ring
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, |A n * f n| < ε := by
    simpa only [Real.norm_eq_abs, norm_zero] using
      hzero.norm.eventually_lt_const (by simpa only [norm_zero] using hε)
  obtain ⟨n, hnzero, hnsmall, hnpos⟩ :=
    (hfreq.and_eventually (hsmall.and (eventually_gt_atTop 0))).exists
  exact ⟨n, hnpos, mul_ne_zero (hA n).ne' hnzero, hnsmall⟩

end ZudilinZeta
end
end

-- Component: missions.zudilin.RootFromPublishedKernel
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta

lemma params13_kernel_scales (n : ℕ) (hn : 1 ≤ n) :
    0 < (n : ℝ) ^ 7 * Real.sqrt (n : ℝ) / (2 * Real.pi) ^ 5 ∧
    0 < (n : ℝ) / (2 * Real.pi) ∧
    ((n : ℝ) / (2 * Real.pi)) /
      ((n : ℝ) ^ 7 * Real.sqrt (n : ℝ) / (2 * Real.pi) ^ 5) ≤ (2 * Real.pi) ^ 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hsp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨by positivity, by positivity, ?_⟩
  have he : ((n : ℝ) / (2 * Real.pi)) /
      ((n : ℝ) ^ 7 * Real.sqrt (n : ℝ) / (2 * Real.pi) ^ 5) =
      (2 * Real.pi) ^ 4 * ((n : ℝ) / ((n : ℝ) ^ 7 * Real.sqrt (n : ℝ))) := by
    field_simp [Real.pi_ne_zero, hnp.ne', hsp.ne']
  rw [he]
  apply mul_le_of_le_one_right (by positivity)
  apply (div_le_one (by positivity)).mpr
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn' (by decide)
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn'
  exact hpow.trans (by nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg hnp.le 7)])

lemma irrational_zeta_of_params13_kernel_contour
    (hcontour : ∀ (τ : ℂ), 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 → ∀ n : ℕ, 2 ≤ n →
      |F params13 n| = (n : ℝ) / (2 * Real.pi) * |(params13KernelIntegral n τ).re|) :
    ∃ k ∈ Finset.Icc 1 4, Irrational (zetaR (3 + 2 * k)) := by
  obtain ⟨τ, hroot, him, hmax, _, hpi⟩ := exists_saddle_root_params13
  obtain ⟨hτ, c, hc, hkernel⟩ := params13_kernel_saddle_limit_nonzero τ hroot him hmax
  have hC0 := (zudilin_numeric_C0_bounds τ hroot him hmax).1
  have hC1 := zudilin_numeric_C1_upper_bound
  have hgap : C1 params13 + (f0 params13 τ).re < 0 := by
    unfold C0 at hC0
    linarith only [hC0, hC1]
  have hexprate : Tendsto (fun n : ℕ =>
      Real.log (Real.exp ((n : ℝ) * (f0 params13 τ).re)) / (n : ℝ))
      atTop (𝓝 (f0 params13 τ).re) := by
    simpa only [exponentialPowerModel, Real.rpow_zero, mul_one, one_mul] using
      exponentialPowerModel_log_rate 1 0 (f0 params13 τ).re zero_lt_one
  have hdecay := tendsto_product_zero_of_log_rates (arithmeticNormalizer params13)
    (fun n => Real.exp ((n : ℝ) * (f0 params13 τ).re))
    (C1 params13) (f0 params13 τ).re (arithmeticNormalizer_pos params13)
    (fun _ _ => Real.exp_pos _) (arithmeticNormalizer_log_tendsto params13) hexprate hgap
  let β : ℕ → ℝ := fun n => (n : ℝ) ^ 7 * Real.sqrt (n : ℝ) / (2 * Real.pi) ^ 5
  have hlim : Tendsto (fun n : ℕ => (β n : ℂ) * Complex.exp (-(n : ℂ) * f0 params13 τ) *
      params13KernelIntegral n τ) atTop (𝓝 c) := by
    simpa [β] using hkernel
  have hsmall := small_nonzero_of_complex_saddle
    (arithmeticNormalizer params13) (F params13) β (fun n => (n : ℝ) / (2 * Real.pi))
    (fun n => params13KernelIntegral n τ) (f0 params13 τ) c
    ((2 * Real.pi) ^ 4) (arithmeticNormalizer_pos params13)
    hc (by positivity)
    (sine_ne_zero_of_phase_nonresonant _ hpi)
    (by filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn; exact params13_kernel_scales n hn)
    (by filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn; exact hcontour τ hτ n hn)
    hlim hdecay
  have hI := zudilin_small_values_criterion params13 rfl
    (by simpa only [← Lambda_eq_arithmeticNormalizer_mul] using hsmall)
  simpa only [params13, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv] using hI

end ZudilinZeta

open ZudilinZeta

lemma zudilin_root_from_kernel_contour
    (hcontour : ∀ (τ : ℂ), 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 → ∀ n : ℕ, 2 ≤ n →
      |F params13 n| = (n : ℝ) / (2 * Real.pi) * |(params13KernelIntegral n τ).re|) :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a = x}).Nonempty := by
  obtain ⟨k, hk, hI⟩ := irrational_zeta_of_params13_kernel_contour hcontour
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
  refine ⟨3 + 2 * k, ?_, ?_⟩
  · interval_cases k <;> norm_num
  · exact ⟨zetaR (3 + 2 * k), hI, zetaR_eq_riemannZeta (3 + 2 * k) (by omega)⟩
end
end


theorem solution :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a = x}).Nonempty := by
  exact zudilin_root_from_kernel_contour ZudilinZeta.params13_contour_formula
