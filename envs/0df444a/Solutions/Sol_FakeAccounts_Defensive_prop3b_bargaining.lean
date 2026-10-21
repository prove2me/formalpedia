-- Prove2me | solution 1 for FakeAccounts.Defensive.prop3b_bargaining
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:36:51.030322+00:00
-- url     : https://prove2.me/submissions/12f56704-bfdc-4f22-96e8-d33ea55bbd6e

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
    ∀ d, 0 ≤ d → StrictMonoOn (fun a => xCsepH { P with lamI := a } d) (Set.Ioi 0) := by
  intro d hd a ha b hb hab
  have hs := tau_pos P hP
  have hc := cost_pos P hP hc0 d hd
  have hΔ := delta_pos P hP
  have hpf := price_pos P hP hp0 d hd
  have hmu := hP.mu_pos
  have hl := hP.l_pos
  have hl1 := hP.l_lt_one
  have h1l : 0 < 1 - P.l ^ 2 := by nlinarith
  show xCsepH { P with lamI := a } d < xCsepH { P with lamI := b } d
  rw [xC_eq, xC_eq]
  show cost P d * (1 / P.qL - 1 / P.qH) * (a * P.mu * (1 - P.l ^ 2) * (price P d)⁻¹ - P.l)
    < cost P d * (1 / P.qL - 1 / P.qH) * (b * P.mu * (1 - P.l ^ 2) * (price P d)⁻¹ - P.l)
  have key : a * P.mu * (1 - P.l ^ 2) * (price P d)⁻¹ - P.l
      < b * P.mu * (1 - P.l ^ 2) * (price P d)⁻¹ - P.l := by
    nlinarith [mul_pos (mul_pos (mul_pos hmu h1l) (inv_pos.2 hpf)) (sub_pos.2 hab)]
  exact mul_lt_mul_of_pos_left key (mul_pos hc hΔ)
