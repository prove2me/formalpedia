-- Prove2me | solution 1 for FakeAccounts.Defensive.prop3a_technology
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:36:49.865139+00:00
-- url     : https://prove2.me/submissions/76261c3d-59ae-447c-8694-33414f854c26

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

set_option autoImplicit false
open FakeAccounts.Platform FakeAccounts.Defensive

lemma xC_eq (P : Params) (d : ℝ) :
    xCsepH P d = cost P d * (1 / P.qL - 1 / P.qH) *
      (P.lamI * P.mu * (1 - P.l ^ 2) * (price P d)⁻¹ - P.l) := by
  unfold xCsepH nCsep2 nIn nUnSep
  ring

lemma tau_ne (P : Params) (hP : Standing P) : (1 - P.tau) ≠ 0 := by
  have := hP.tau_lt_one; intro h; linarith

lemma tau_pos (P : Params) (hP : Standing P) : 0 < 1 - P.tau := by
  have := hP.tau_lt_one; linarith

lemma qH_pos (P : Params) (hP : Standing P) : 0 < P.qH :=
  lt_trans hP.qL_pos hP.qL_lt_qH

lemma price_pos (P : Params) (hP : Standing P) (hp0 : 0 < P.p0) (d : ℝ) (hd : 0 ≤ d) :
    0 < price P d := by
  unfold price
  have := tau_pos P hP
  have : 0 ≤ d / (1 - P.tau) := div_nonneg hd this.le
  linarith

lemma cost_pos (P : Params) (hP : Standing P) (hc0 : 0 < P.c0) (d : ℝ) (hd : 0 ≤ d) :
    0 < cost P d := by
  unfold cost
  have := tau_pos P hP
  have := hP.c1_nonneg
  have : 0 ≤ P.c1 * (1 - P.tau) * d := by positivity
  linarith

lemma delta_pos (P : Params) (hP : Standing P) : 0 < 1 / P.qL - 1 / P.qH := by
  have h1 := hP.qL_pos
  have h2 := qH_pos P hP
  have h3 := hP.qL_lt_qH
  rw [sub_pos]
  exact one_div_lt_one_div_of_lt h1 h3

lemma K_pos (P : Params) (hP : Standing P) : 0 < P.lamI * P.mu * (1 - P.l ^ 2) := by
  have h1 := hP.lamI_pos
  have h2 := hP.mu_pos
  have h3 := hP.l_pos
  have h4 := hP.l_lt_one
  have : 0 < 1 - P.l ^ 2 := by nlinarith
  positivity

lemma hasDerivAt_xC (P : Params) (hP : Standing P) (d : ℝ) (hpf : price P d ≠ 0) :
    HasDerivAt (xCsepH P)
      (-(1 / (1 - P.tau)) * (P.lamI * P.mu * (1 - P.l ^ 2) / price P d ^ 2) *
          ((P.qH - P.qL) / (P.qH * P.qL)) * cost P d
        + P.c1 * (1 - P.tau) * ((P.lamI * P.mu * (1 - P.l ^ 2) - price P d * P.l) / price P d) *
          ((P.qH - P.qL) / (P.qH * P.qL))) d := by
  have hs := tau_ne P hP
  have hqL := hP.qL_pos.ne'
  have hqH := (qH_pos P hP).ne'
  have hc : HasDerivAt (cost P) (P.c1 * (1 - P.tau)) d := by
    have : HasDerivAt (fun x => P.c0 + P.c1 * (1 - P.tau) * x) (P.c1 * (1 - P.tau)) d := by
      simpa using ((hasDerivAt_id d).const_mul (P.c1 * (1 - P.tau))).const_add P.c0
    exact this
  have hp : HasDerivAt (price P) (1 / (1 - P.tau)) d := by
    have : HasDerivAt (fun x => P.p0 + x / (1 - P.tau)) (1 / (1 - P.tau)) d := by
      simpa using ((hasDerivAt_id d).div_const (1 - P.tau)).const_add P.p0
    exact this
  have hinv := hp.inv hpf
  have hmain := (hc.mul_const (1 / P.qL - 1 / P.qH)).mul
    ((hinv.const_mul (P.lamI * P.mu * (1 - P.l ^ 2))).sub_const P.l)
  have heq : xCsepH P = fun x => cost P x * (1 / P.qL - 1 / P.qH) *
      (P.lamI * P.mu * (1 - P.l ^ 2) * (price P x)⁻¹ - P.l) := funext (xC_eq P)
  rw [heq]
  refine hmain.congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp
  ring

noncomputable def Gf (P : Params) (u : ℝ) : ℝ :=
  P.c1 * (1 - P.tau) ^ 2 * (P.lamI * P.mu * (1 - P.l ^ 2) * P.p0 - P.l * u ^ 2)
    - P.lamI * P.mu * (1 - P.l ^ 2) * P.c0

lemma hasDerivAt_G (P : Params) (hP : Standing P) (d : ℝ) (hpf : price P d ≠ 0) :
    HasDerivAt (xCsepH P)
      ((P.qH - P.qL) / (P.qH * P.qL) / ((1 - P.tau) * price P d ^ 2) * Gf P (price P d)) d := by
  have hs := tau_ne P hP
  have hqL := hP.qL_pos.ne'
  have hqH := (qH_pos P hP).ne'
  refine (hasDerivAt_xC P hP d hpf).congr_deriv ?_
  unfold Gf
  unfold cost
  have hpf' := hpf
  unfold price at hpf' ⊢
  field_simp
  ring

lemma strictMonoOn_of_G (P : Params) (hP : Standing P) (hp0 : 0 < P.p0) (a b : ℝ) (ha : 0 ≤ a)
    (hG : ∀ d ∈ Set.Ioo a b, 0 < Gf P (price P d)) :
    StrictMonoOn (xCsepH P) (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · intro x hx
    exact (hasDerivAt_xC P hP x (price_pos P hP hp0 x (ha.trans hx.1)).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := ha.trans hx.1.le
    have hpp := price_pos P hP hp0 x hx0
    rw [(hasDerivAt_G P hP x hpp.ne').deriv]
    have h1 := tau_pos P hP
    have h2 := qH_pos P hP
    have h3 := hP.qL_pos
    have h4 : 0 < (P.qH - P.qL) / (P.qH * P.qL) := div_pos (by linarith [hP.qL_lt_qH]) (by positivity)
    exact mul_pos (div_pos h4 (by positivity)) (hG x hx)

lemma strictAntiOn_of_G (P : Params) (hP : Standing P) (hp0 : 0 < P.p0) (a b : ℝ) (ha : 0 ≤ a)
    (hG : ∀ d ∈ Set.Ioo a b, Gf P (price P d) < 0) :
    StrictAntiOn (xCsepH P) (Set.Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
  · intro x hx
    exact (hasDerivAt_xC P hP x (price_pos P hP hp0 x (ha.trans hx.1)).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := ha.trans hx.1.le
    have hpp := price_pos P hP hp0 x hx0
    rw [(hasDerivAt_G P hP x hpp.ne').deriv]
    have h1 := tau_pos P hP
    have h2 := qH_pos P hP
    have h3 := hP.qL_pos
    have h4 : 0 < (P.qH - P.qL) / (P.qH * P.qL) := div_pos (by linarith [hP.qL_lt_qH]) (by positivity)
    have h5 : 0 < (P.qH - P.qL) / (P.qH * P.qL) / ((1 - P.tau) * price P x ^ 2) := div_pos h4 (by positivity)
    exact mul_neg_of_pos_of_neg h5 (hG x hx)

theorem solution (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0) :
    ∀ d, 0 < d → ∀ t₁ t₂, 0 ≤ t₁ → t₁ < t₂ → t₂ < 1 → FakeAccounts.Platform.price { P with tau := t₂ } d ≤ FakeAccounts.Platform.eta2 P →
      xCsepH { P with tau := t₂ } d < xCsepH { P with tau := t₁ } d := by
  intro d hd t₁ t₂ ht1 ht12 ht2 hle
  have hc1 := hP.c1_nonneg
  have hl := hP.l_pos
  have hΔ := delta_pos P hP
  have hKp := K_pos P hP
  have hs1 : 0 < 1 - t₁ := by linarith
  have hs2 : 0 < 1 - t₂ := by linarith
  have hη : eta2 P * P.l = P.lamI * P.mu * (1 - P.l ^ 2) := by unfold eta2; field_simp
  show xCsepH { P with tau := t₂ } d < xCsepH { P with tau := t₁ } d
  rw [xC_eq, xC_eq]
  show cost { P with tau := t₂ } d * (1 / P.qL - 1 / P.qH) *
        (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ - P.l)
      < cost { P with tau := t₁ } d * (1 / P.qL - 1 / P.qH) *
        (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₁ } d)⁻¹ - P.l)
  have e1 : cost { P with tau := t₂ } d = P.c0 + P.c1 * (1 - t₂) * d := rfl
  have e2 : cost { P with tau := t₁ } d = P.c0 + P.c1 * (1 - t₁) * d := rfl
  have e3 : price { P with tau := t₂ } d = P.p0 + d / (1 - t₂) := rfl
  have e4 : price { P with tau := t₁ } d = P.p0 + d / (1 - t₁) := rfl
  have hcc2 : 0 < cost { P with tau := t₂ } d := by
    rw [e1]; have : 0 ≤ P.c1 * (1 - t₂) * d := by positivity
    linarith
  have hcc : cost { P with tau := t₂ } d ≤ cost { P with tau := t₁ } d := by
    rw [e1, e2]; nlinarith [mul_nonneg (mul_nonneg hc1 hd.le) (sub_nonneg.2 ht12.le)]
  have hdd : d / (1 - t₁) < d / (1 - t₂) := div_lt_div_of_pos_left hd hs2 (by linarith)
  have hd1 : 0 < d / (1 - t₁) := div_pos hd hs1
  have hp1 : 0 < price { P with tau := t₁ } d := by rw [e4]; linarith
  have hp2 : 0 < price { P with tau := t₂ } d := by rw [e3]; have := div_pos hd hs2; linarith
  have hpp : price { P with tau := t₁ } d < price { P with tau := t₂ } d := by rw [e3, e4]; linarith
  have hinv : (price { P with tau := t₂ } d)⁻¹ < (price { P with tau := t₁ } d)⁻¹ :=
    inv_strictAnti₀ hp1 hpp
  have hB2 : 0 ≤ P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ - P.l := by
    have h1 : P.l ≤ P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp2]
      nlinarith
    linarith
  have hB : P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ - P.l
      < P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₁ } d)⁻¹ - P.l := by
    have := mul_lt_mul_of_pos_left hinv hKp
    linarith
  have hcc1 : 0 < cost { P with tau := t₁ } d := lt_of_lt_of_le hcc2 hcc
  have key : cost { P with tau := t₂ } d *
        (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ - P.l)
      < cost { P with tau := t₁ } d *
        (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₁ } d)⁻¹ - P.l) := by
    calc _ ≤ cost { P with tau := t₁ } d *
          (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ - P.l) :=
            mul_le_mul_of_nonneg_right hcc hB2
      _ < _ := mul_lt_mul_of_pos_left hB hcc1
  calc _ = (1 / P.qL - 1 / P.qH) * (cost { P with tau := t₂ } d *
          (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₂ } d)⁻¹ - P.l)) := by ring
    _ < (1 / P.qL - 1 / P.qH) * (cost { P with tau := t₁ } d *
          (P.lamI * P.mu * (1 - P.l ^ 2) * (price { P with tau := t₁ } d)⁻¹ - P.l)) :=
        mul_lt_mul_of_pos_left key hΔ
    _ = _ := by ring
