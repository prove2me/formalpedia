-- Prove2me | solution 1 for EulerProduct.three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/13b5350e-bd95-5e30-97aa-aa40dceead42

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one

set_option autoImplicit false

open Complex

namespace R1LogDer341

section EulerLogDeriv

lemma norm_coeff_le (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ ≤ 1) (z : ℂ) :
    ‖c * (N : ℂ) ^ (-z)‖ ≤ (N : ℝ) ^ (-z.re) := by
  rw [norm_mul, norm_natCast_cpow_of_pos (by omega), neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc

lemma rpow_neg_le_rpow_neg (N : ℕ) (hN : 2 ≤ N) {σ σ' : ℝ} (h : σ' ≤ σ) :
    (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ') := by
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (by omega : 1 ≤ N)
  · linarith

lemma rpow_neg_le_half (N : ℕ) (hN : 2 ≤ N) (σ : ℝ) (hσ : 1 ≤ σ) : (N : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := rpow_neg_le_rpow_neg N hN hσ
  have h2 : (N : ℝ) ^ (-(1 : ℝ)) = 1 / N := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_one, one_div]
  have h3 : (1 : ℝ) / N ≤ 1 / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact one_div_le_one_div_of_le (by norm_num) this
  linarith [h1, h2.le, h2.ge, h3]

theorem main {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s ∧
    (∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 ∧
    HasSum (fun i => (Real.log (N i) : ℂ) * (c i * ((N i : ℕ) : ℂ) ^ (-s)) /
        (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
      (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s /
          ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹)) := by
  set a : ι → ℂ → ℂ := fun i z => c i * ((N i : ℕ) : ℂ) ^ (-z) with ha
  set g : ι → ℂ → ℂ := fun i z => -log (1 - a i z) with hg
  set G : ℂ → ℂ := fun z => ∑' i, g i z with hG
  set E : ℂ → ℂ := fun z => ∏' i, (1 - a i z)⁻¹ with hE
  set σ₁ : ℝ := (1 + s.re) / 2 with hσ₁
  have hσ₁1 : 1 < σ₁ := by rw [hσ₁]; linarith
  have hσ₁s : σ₁ < s.re := by rw [hσ₁]; linarith
  set U : Set ℂ := {z : ℂ | σ₁ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hσ₁s
  have hN0 : ∀ i, (N i : ℂ) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (by have := hN i; omega)

  have hnorm_a : ∀ i, ∀ z ∈ U, ‖a i z‖ ≤ ((N i : ℕ) : ℝ) ^ (-σ₁) := by
    intro i z hz
    have hz' : σ₁ ≤ z.re := le_of_lt hz
    exact (norm_coeff_le (N i) (hN i) (c i) (hc i) z).trans (rpow_neg_le_rpow_neg (N i) (hN i) hz')
  have hhalf : ∀ i, ∀ z ∈ U, ‖a i z‖ ≤ 1 / 2 := fun i z hz =>
    (hnorm_a i z hz).trans (rpow_neg_le_half (N i) (hN i) σ₁ hσ₁1.le)
  have hne : ∀ i, ∀ z ∈ U, 1 - a i z ≠ 0 := by
    intro i z hz h0
    have : a i z = 1 := (sub_eq_zero.mp h0).symm
    have h1 := hhalf i z hz
    rw [this, norm_one] at h1
    norm_num at h1
  have hslit : ∀ i, ∀ z ∈ U, 1 - a i z ∈ slitPlane := by
    intro i z hz
    rw [sub_eq_add_neg]
    apply mem_slitPlane_of_norm_lt_one
    rw [norm_neg]
    linarith [hhalf i z hz]

  have hda : ∀ i z, HasDerivAt (a i) (-(Real.log (N i) : ℂ) * a i z) z := by
    intro i z
    have h1 : HasDerivAt (fun z : ℂ => -z) (-1) z := (hasDerivAt_id z).neg
    have h2 : HasDerivAt (fun z : ℂ => ((N i : ℕ) : ℂ) ^ (-z))
        (((N i : ℕ) : ℂ) ^ (-z) * log ((N i : ℕ) : ℂ) * (-1)) z :=
      h1.const_cpow (Or.inl (hN0 i))
    have h3 := h2.const_mul (c i)
    have hval : c i * (((N i : ℕ) : ℂ) ^ (-z) * log ((N i : ℕ) : ℂ) * (-1))
        = -(Real.log (N i) : ℂ) * a i z := by
      rw [natCast_log]
      simp only [ha]
      ring
    rw [hval] at h3
    exact h3
  have hdg : ∀ i, ∀ z ∈ U,
      HasDerivAt (g i) (-((Real.log (N i) : ℂ) * a i z / (1 - a i z))) z := by
    intro i z hz
    have h1 : HasDerivAt (fun w => 1 - a i w) (-(-(Real.log (N i) : ℂ) * a i z)) z :=
      (hda i z).const_sub 1
    have h2 := h1.clog (hslit i z hz)
    have h3 := h2.neg
    have hval : -(-(-(Real.log (N i) : ℂ) * a i z) / (1 - a i z))
        = -((Real.log (N i) : ℂ) * a i z / (1 - a i z)) := by ring
    rw [hval] at h3
    exact h3
  have hgdiff : ∀ i, DifferentiableOn ℂ (g i) U :=
    fun i z hz => (hdg i z hz).differentiableAt.differentiableWithinAt
  have hgle : ∀ i, ∀ z ∈ U, ‖g i z‖ ≤ 3 / 2 * ((N i : ℕ) : ℝ) ^ (-σ₁) := by
    intro i z hz
    have h1 : ‖log (1 + -a i z)‖ ≤ 3 / 2 * ‖-a i z‖ :=
      norm_log_one_add_half_le_self (by rw [norm_neg]; exact hhalf i z hz)
    rw [← sub_eq_add_neg, norm_neg] at h1
    calc ‖g i z‖ = ‖log (1 - a i z)‖ := by simp [hg]
      _ ≤ 3 / 2 * ‖a i z‖ := h1
      _ ≤ 3 / 2 * ((N i : ℕ) : ℝ) ^ (-σ₁) := by gcongr; exact hnorm_a i z hz
  have hu : Summable fun i => 3 / 2 * ((N i : ℕ) : ℝ) ^ (-σ₁) := (hsum σ₁ hσ₁1).mul_left _

  have hGsum : HasSum (fun i => deriv (g i) s) (deriv G s) :=
    hasSum_deriv_of_summable_norm hu hgdiff hUo hgle hsU
  have hGdiff : DifferentiableOn ℂ G U := differentiableOn_tsum_of_summable_norm hu hgdiff hUo hgle

  have hEG : ∀ z ∈ U, E z = exp (G z) := by
    intro z hz
    have hsz : Summable fun i => g i z :=
      Summable.of_norm_bounded hu (fun i => hgle i z hz)
    have H := hsz.hasSum.cexp.tprod_eq
    have hcongr : (cexp ∘ fun i => g i z) = fun i => (1 - a i z)⁻¹ := by
      funext i
      simp only [Function.comp_apply, hg, exp_neg, exp_log (hne i z hz)]
    rw [hcongr] at H
    exact H
  have hEev : E =ᶠ[nhds s] fun z => exp (G z) :=
    Filter.eventuallyEq_of_mem (hUo.mem_nhds hsU) hEG
  have hGs : HasDerivAt G (deriv G s) s := (hGdiff.differentiableAt (hUo.mem_nhds hsU)).hasDerivAt
  have hexpG : HasDerivAt (fun z => exp (G z)) (exp (G s) * deriv G s) s := hGs.cexp
  have hEderiv : HasDerivAt E (exp (G s) * deriv G s) s := hexpG.congr_of_eventuallyEq hEev
  have hEs : E s = exp (G s) := hEG s hsU
  refine ⟨hEderiv.differentiableAt, ?_, ?_⟩
  · show E s ≠ 0
    rw [hEs]
    exact exp_ne_zero _
  · have h1 : -(deriv E s / E s) = -deriv G s := by
      rw [hEderiv.deriv, hEs, mul_div_cancel_left₀ _ (exp_ne_zero _)]
    have h2 : ∀ i, deriv (g i) s = -((Real.log (N i) : ℂ) * a i s / (1 - a i s)) :=
      fun i => (hdg i s hsU).deriv
    have h3 := hGsum.neg
    have h4 : (fun i => -deriv (g i) s) = fun i => (Real.log (N i) : ℂ) * a i s / (1 - a i s) := by
      funext i
      rw [h2 i, neg_neg]
    rw [h4] at h3
    show HasSum (fun i => (Real.log (N i) : ℂ) * a i s / (1 - a i s)) (-(deriv E s / E s))
    rw [h1]
    exact h3

end EulerLogDeriv

theorem kernel_nonneg {w : ℂ} (hw : ‖w‖ ≤ 1) : 0 ≤ 3 + 4 * w.re + (w ^ 2).re := by
  have h1 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [sq, mul_re]
  have h2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  rw [h1]
  nlinarith [sq_nonneg (w.re + 1)]

theorem kernel_nonneg' {w : ℂ} (hw : ‖w‖ ≤ 1) : 0 ≤ 3 + w.re := by
  have := (abs_re_le_norm w).trans hw
  have := neg_abs_le w.re
  linarith

theorem hasSum_geom_shift {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => w ^ (n + 1)) (w / (1 - w)) := by
  have h := (hasSum_geometric_of_norm_lt_one hw).mul_left w
  have h1 : (fun n : ℕ => w * w ^ n) = fun n : ℕ => w ^ (n + 1) := by
    funext n
    rw [pow_succ']
  rw [h1] at h
  rw [div_eq_mul_inv]
  exact h

theorem re_geom_comb_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {z z₂ : ℂ} (hz : ‖z‖ ≤ 1)
    (hz₂ : ‖z₂‖ ≤ 1) (hzz : z = 0 ∨ z₂ = z ^ 2) :
    0 ≤ 3 * ((x : ℂ) / (1 - x)).re + 4 * ((x : ℂ) * z / (1 - x * z)).re
      + ((x : ℂ) * z₂ / (1 - x * z₂)).re := by
  have hxc : ‖(x : ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀]; exact hx₁
  have hxz : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul]
    calc ‖(x : ℂ)‖ * ‖z‖ ≤ ‖(x : ℂ)‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hxc
  have hxz₂ : ‖(x : ℂ) * z₂‖ < 1 := by
    rw [norm_mul]
    calc ‖(x : ℂ)‖ * ‖z₂‖ ≤ ‖(x : ℂ)‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hxc
  rw [← ((hasSum_re <| hasSum_geom_shift hxc).mul_left 3).add
    ((hasSum_re <| hasSum_geom_shift hxz).mul_left 4) |>.add
    (hasSum_re <| hasSum_geom_shift hxz₂) |>.tsum_eq]
  refine tsum_nonneg fun k ↦ ?_
  simp only [mul_pow]
  set n := k + 1 with hn
  have hnpos : 0 < n := Nat.succ_pos k
  have hxn : ((x : ℂ) ^ n).re = x ^ n := by rw [← ofReal_pow, ofReal_re]
  have hxn' : ((x : ℂ) ^ n).im = 0 := by rw [← ofReal_pow, ofReal_im]
  have hA : ((x : ℂ) ^ n * z ^ n).re = x ^ n * (z ^ n).re := by
    rw [mul_re, hxn, hxn', zero_mul, sub_zero]
  have hB : ((x : ℂ) ^ n * z₂ ^ n).re = x ^ n * (z₂ ^ n).re := by
    rw [mul_re, hxn, hxn', zero_mul, sub_zero]
  rw [hxn, hA, hB]
  have hxpow : 0 ≤ x ^ n := pow_nonneg hx₀ n
  rcases hzz with hz0 | hz2
  · subst hz0
    have hw : ‖z₂ ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz₂
    have := kernel_nonneg' hw
    rw [zero_pow hnpos.ne', zero_re, mul_zero, mul_zero, add_zero]
    nlinarith
  · subst hz2
    have hw : ‖z ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
    have := kernel_nonneg hw
    rw [← pow_mul, mul_comm 2 n, pow_mul]
    nlinarith

theorem natCast_cpow_neg_add (n : ℕ) (hn : n ≠ 0) (σ : ℝ) (τ : ℂ) :
    (n : ℂ) ^ (-((σ : ℂ) + τ)) = ((n : ℝ) ^ (-σ) : ℝ) * (n : ℂ) ^ (-τ) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [neg_add, cpow_add _ _ hn', ofReal_cpow (Nat.cast_nonneg n) (-σ)]
  simp

theorem norm_natCast_cpow_neg_mul_I (n : ℕ) (hn : n ≠ 0) (u : ℝ) :
    ‖(n : ℂ) ^ (-((u : ℂ) * I))‖ = 1 := by
  rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

theorem main341
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i)
    (c c₂ : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) (hc₂ : ∀ i, ‖c₂ i‖ ≤ 1)
    (hcc : ∀ i, c i = 0 ∨ c₂ i = c i ^ 2)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv (fun z : ℂ => ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-z))⁻¹) (σ : ℂ) /
              ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      + 4 * (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + t * Complex.I) /
              ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I)))⁻¹)).re
      + (-(deriv (fun z : ℂ => ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + 2 * t * Complex.I) /
              ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * t * Complex.I)))⁻¹)).re := by
  have hN0 : ∀ i, N i ≠ 0 := fun i => by have := hN i; omega

  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + 2 * t * Complex.I).re := by simpa using hσ
  obtain ⟨-, -, h0⟩ := main N hN (fun _ => (1 : ℂ)) (fun _ => by simp) hsum (σ : ℂ) hs0
  obtain ⟨-, -, h1⟩ := main N hN c hc hsum ((σ : ℂ) + t * Complex.I) hs1
  obtain ⟨-, -, h2⟩ := main N hN c₂ hc₂ hsum ((σ : ℂ) + 2 * t * Complex.I) hs2
  simp only [one_mul] at h0
  rw [← ((hasSum_re h0).mul_left 3).add ((hasSum_re h1).mul_left 4) |>.add (hasSum_re h2) |>.tsum_eq]
  refine tsum_nonneg fun i ↦ ?_

  set x : ℝ := ((N i : ℕ) : ℝ) ^ (-σ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx1 : x < 1 := by
    rw [hx, Real.rpow_neg (Nat.cast_nonneg _), inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow (by exact_mod_cast (hN i)) (by linarith)
  set z : ℂ := c i * ((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I)) with hz
  set z₂ : ℂ := c₂ i * ((N i : ℕ) : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) with hz₂
  have hzn : ‖z‖ ≤ 1 := by
    rw [hz, norm_mul, norm_natCast_cpow_neg_mul_I _ (hN0 i), mul_one]; exact hc i
  have hz₂n : ‖z₂‖ ≤ 1 := by
    rw [hz₂, norm_mul, norm_natCast_cpow_neg_mul_I _ (hN0 i), mul_one]; exact hc₂ i
  have hzz : z = 0 ∨ z₂ = z ^ 2 := by
    rcases hcc i with h | h
    · left; rw [hz, h, zero_mul]
    · right
      rw [hz₂, hz, mul_pow, ← h, ← cpow_nat_mul]
      congr 2
      push_cast
      ring
  have e0 : ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) = (x : ℂ) := by
    rw [hx, ofReal_cpow (Nat.cast_nonneg _) (-σ)]; simp
  have e1 : c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I)) = (x : ℂ) * z := by
    rw [natCast_cpow_neg_add _ (hN0 i), hz, hx]
    ring
  have e2 : c₂ i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * t * I)) = (x : ℂ) * z₂ := by
    have : (σ : ℂ) + 2 * t * I = (σ : ℂ) + (((2 * t : ℝ) : ℂ) * I) := by push_cast; ring
    rw [this, natCast_cpow_neg_add _ (hN0 i), hz₂, hx]
    ring
  rw [e0, e1, e2]

  have hL : 0 ≤ Real.log (N i) := Real.log_nonneg (by exact_mod_cast (by have := hN i; omega : 1 ≤ N i))
  have hre : ∀ w : ℂ, ((Real.log (N i) : ℂ) * w).re = Real.log (N i) * w.re := fun w =>
    re_ofReal_mul _ _
  have hre' : ∀ w v : ℂ, ((Real.log (N i) : ℂ) * w / v).re = Real.log (N i) * (w / v).re := fun w v => by
    rw [mul_div_assoc, hre]
  rw [hre', hre', hre']
  have := re_geom_comb_nonneg hx0 hx1 hzn hz₂n hzz
  nlinarith

end R1LogDer341

theorem solution
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i)
    (c c₂ : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) (hc₂ : ∀ i, ‖c₂ i‖ ≤ 1)
    (hcc : ∀ i, c i = 0 ∨ c₂ i = c i ^ 2)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv (fun z : ℂ => ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-z))⁻¹) (σ : ℂ) /
              ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      + 4 * (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + t * Complex.I) /
              ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I)))⁻¹)).re
      + (-(deriv (fun z : ℂ => ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + 2 * t * Complex.I) /
              ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * t * Complex.I)))⁻¹)).re :=
  R1LogDer341.main341 N hN c c₂ hc hc₂ hcc hsum σ t hσ

end S_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
end P2MW
export P2MW.S_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one (solution)
