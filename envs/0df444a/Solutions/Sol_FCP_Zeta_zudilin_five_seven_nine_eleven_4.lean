-- Prove2me | solution 4 for FCP.Zeta.zudilin_five_seven_nine_eleven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T19:33:08.733831+00:00
-- url     : https://prove2.me/submissions/b5bf6d16-7e29-497c-9de6-c0b13011a6a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZudilinZeta_zudilin_lcm_asymptotics
import Theorems.Thm_ZudilinZeta_zudilin_phi_log_growth_fixed
import Theorems.Thm_ZudilinZeta_zudilin_phi_tail_integral_eq
import Theorems.Thm_ZudilinZeta_zudilin_small_values_criterion
import Theorems.Thm_ZudilinZeta_exists_saddle_root_params13
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_bounds
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C1_upper_bound
import Theorems.Thm_ZudilinZeta_zudilin_lemma2
import Theorems.Thm_ZudilinZeta_zetaR_eq_riemannZeta

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

section
set_option autoImplicit false
open Filter
open scoped Topology

namespace ZudilinZeta

lemma real_isBoundedUnder_of_limsup_ne_zero (f : ℕ → ℝ)
    (h : Filter.limsup f atTop≠0) :
    Filter.IsBoundedUnder (fun x y : ℝ => x≤y) atTop f := by
  by_contra hbad
  exact h (Real.limsup_of_not_isBoundedUnder hbad)

lemma eventually_nonzero_of_negative_log_limsup (f : ℕ → ℝ)
    (h : Filter.limsup (fun n : ℕ => Real.log |f n|/(n : ℝ)) atTop<0) :
    ∀ᶠ n : ℕ in atTop, f n≠0 := by
  have hb := real_isBoundedUnder_of_limsup_ne_zero _ h.ne
  have hh := eventually_lt_of_limsup_lt h hb
  filter_upwards [hh] with n hn
  intro hz
  simp only [hz, abs_zero, Real.log_zero, zero_div] at hn
  exact lt_irrefl _ hn

lemma small_nonzero_products_of_negative_log_limsup
    (A f : ℕ → ℝ) (a r : ℝ)
    (hApos : ∀ n : ℕ, 0<A n)
    (hAlim : Tendsto (fun n : ℕ => Real.log (A n)/(n : ℝ)) atTop (𝓝 a))
    (hlimsup : Filter.limsup (fun n : ℕ => Real.log |f n|/(n : ℝ)) atTop=r)
    (hr : r<0) (hgap : a+r<0) :
    ∀ ε : ℝ, 0<ε → ∃ n : ℕ, 0<n ∧ A n*f n≠0 ∧ |A n*f n|<ε := by
  have hnegative : Filter.limsup (fun n : ℕ => Real.log |f n|/(n : ℝ)) atTop<0 := by
    rwa [hlimsup]
  have hbounded := real_isBoundedUnder_of_limsup_ne_zero _ hnegative.ne
  have hnonzero := eventually_nonzero_of_negative_log_limsup f hnegative
  let δ : ℝ := -(a+r)/4
  have hδ : 0<δ := by dsimp [δ]; linarith only [hgap]
  let c : ℝ := (a+r)/2
  have hc : c<0 := by dsimp [c]; linarith only [hgap]
  have hF : ∀ᶠ n : ℕ in atTop, Real.log |f n|/(n : ℝ)<r+δ := by
    apply eventually_lt_of_limsup_lt _ hbounded
    rw [hlimsup]
    linarith only [hδ]
  have hA : ∀ᶠ n : ℕ in atTop, Real.log (A n)/(n : ℝ)<a+δ :=
    hAlim.eventually_lt_const (by linarith only [hδ])
  have hexp : Tendsto (fun n : ℕ => Real.exp (c*(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.exp (c*(n : ℝ))<ε :=
    hexp.eventually_lt_const hε
  obtain ⟨n, hnzero, hnF, hnA, hnsmall, hnpos⟩ :=
    (hnonzero.and (hF.and (hA.and (hsmall.and (eventually_gt_atTop 0))))).exists
  have hn : (0 : ℝ)<n := by exact_mod_cast hnpos
  have hprod : A n*f n≠0 := mul_ne_zero (hApos n).ne' hnzero
  have hlog : Real.log |A n*f n|=Real.log (A n)+Real.log |f n| := by
    rw [abs_mul, abs_of_pos (hApos n), Real.log_mul (hApos n).ne' (abs_pos.mpr hnzero).ne']
  refine ⟨n, hnpos, hprod, ?_⟩
  have hrate : Real.log |A n*f n|/(n : ℝ)<c := by
    rw [hlog, add_div]
    dsimp [c, δ] at *
    linarith only [hnA, hnF]
  have hvalue : |A n*f n|<Real.exp (c*(n : ℝ)) := by
    rw [← Real.exp_log (abs_pos.mpr hprod)]
    exact Real.exp_lt_exp.mpr ((div_lt_iff₀ hn).mp hrate)
  exact hvalue.trans hnsmall

lemma irrational_zeta_of_negative_log_limsup (P : Params) (hr : P.r=3) (τ : ℂ)
    (hC : C1 P<C0 P τ) (hCpos : 0<C0 P τ)
    (hlimsup : Filter.limsup (fun n : ℕ => Real.log |F P n|/(n : ℝ)) atTop=
      (f0 P τ).re) :
    ∃ k∈Finset.Icc 1 ((P.q-P.r-2)/2), Irrational (zetaR (P.r+2*k)) := by
  have hrate : (f0 P τ).re<0 := by
    unfold C0 at hCpos
    linarith only [hCpos]
  have hgap : C1 P+(f0 P τ).re<0 := by
    unfold C0 at hC
    linarith only [hC]
  have hs := small_nonzero_products_of_negative_log_limsup (arithmeticNormalizer P)
    (F P) (C1 P) (f0 P τ).re (arithmeticNormalizer_pos P)
    (arithmeticNormalizer_log_tendsto P) hlimsup hrate hgap
  apply zudilin_small_values_criterion P hr
  simpa only [← Lambda_eq_arithmeticNormalizer_mul] using hs

end ZudilinZeta
end

section
set_option autoImplicit false
open ZudilinZeta

lemma zudilin_root_from_lemma2 :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a=x}).Nonempty := by
  obtain ⟨τ, hroot, him, hmax, hre, hpi⟩ := exists_saddle_root_params13
  have hC0 := (zudilin_numeric_C0_bounds τ hroot him hmax).1
  have hC1 := zudilin_numeric_C1_upper_bound
  have hC : C1 params13<C0 params13 τ := by linarith only [hC0, hC1]
  have hCpos : 0<C0 params13 τ := by linarith only [hC0]
  have hlimsup := zudilin_lemma2 params13 rfl τ hroot him hmax hre hpi
  obtain ⟨k, hk, hI⟩ := irrational_zeta_of_negative_log_limsup params13 rfl τ hC hCpos hlimsup
  have hk' : 1≤k ∧ k≤4 := by simpa [Finset.mem_Icc, params13] using hk
  obtain ⟨hklo, hkhi⟩ := hk'
  have hI' : Irrational (zetaR (3+2*k)) := by simpa [params13] using hI
  refine ⟨3+2*k, ?_, ?_⟩
  · interval_cases k <;> norm_num
  · exact ⟨zetaR (3+2*k), hI', zetaR_eq_riemannZeta (3+2*k) (by omega)⟩
end

theorem solution :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a=x}).Nonempty := by
  exact zudilin_root_from_lemma2
