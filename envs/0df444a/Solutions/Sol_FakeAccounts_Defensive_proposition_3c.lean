-- Prove2me | solution 1 for FakeAccounts.Defensive.proposition_3c
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:36:52.40086+00:00
-- url     : https://prove2.me/submissions/ffd12162-487a-4682-a902-7bb16971423b

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

theorem solution (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0)
    (hA3 : P.p0 < FakeAccounts.Platform.eta2 P) :
    (P.c1 * (1 - P.tau) ^ 2 ≤ P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) →
      StrictAntiOn (xCsepH P) (Set.Icc 0 (FakeAccounts.Platform.d2 P))) ∧
    (P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) < P.c1 * (1 - P.tau) ^ 2 →
      ∃ dh, 0 < dh ∧ dh < FakeAccounts.Platform.d2 P ∧ StrictMonoOn (xCsepH P) (Set.Icc 0 dh) ∧
        StrictAntiOn (xCsepH P) (Set.Icc dh (FakeAccounts.Platform.d2 P))) := by
  have hs := tau_pos P hP
  have hl := hP.l_pos
  have hKp := K_pos P hP
  have hc1 := hP.c1_nonneg
  have hη : eta2 P * P.l = P.lamI * P.mu * (1 - P.l ^ 2) := by unfold eta2; field_simp
  have hD : 0 < P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l) :=
    mul_pos hp0 (by nlinarith)
  have hprice : ∀ d, price P d = P.p0 + d / (1 - P.tau) := fun d => rfl
  have hd2pos : 0 < d2 P := by unfold d2; exact mul_pos hs (by linarith)
  refine ⟨?_, ?_⟩
  · intro h22
    have h22' := (le_div_iff₀ hD).1 h22
    apply strictAntiOn_of_G P hP hp0 0 (d2 P) le_rfl
    intro d hd
    have hdp : 0 < d / (1 - P.tau) := div_pos hd.1 hs
    have hu : P.p0 < price P d := by rw [hprice]; linarith
    unfold Gf
    rcases hc1.eq_or_lt with h0 | hpos
    · rw [← h0]; nlinarith [mul_pos hKp hc0]
    · have ha : 0 < P.c1 * (1 - P.tau) ^ 2 := by positivity
      have hu2 : P.p0 ^ 2 < price P d ^ 2 := by nlinarith
      nlinarith [mul_pos (mul_pos ha hl) (sub_pos.2 hu2)]
  · intro h
    set a := P.c1 * (1 - P.tau) ^ 2 with ha_def
    have h' := (div_lt_iff₀ hD).1 h
    have ha : 0 < a := by
      by_contra hcon
      push Not at hcon
      have : 0 < P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 := mul_pos hKp hc0
      nlinarith
    have hal : 0 < a * P.l := mul_pos ha hl
    set w := (a * (P.lamI * P.mu * (1 - P.l ^ 2)) * P.p0 - P.lamI * P.mu * (1 - P.l ^ 2) * P.c0) / (a * P.l) with hw_def
    have hw : a * P.l * w = a * (P.lamI * P.mu * (1 - P.l ^ 2)) * P.p0 - P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 := by
      rw [hw_def]; field_simp
    have hGf : ∀ u, Gf P u = a * P.l * (w - u ^ 2) := by
      intro u; unfold Gf; rw [← ha_def]; nlinarith [hw]
    have hlow : P.p0 ^ 2 < w := by
      by_contra hcon
      push Not at hcon
      have := mul_nonneg hal.le (sub_nonneg.2 hcon)
      nlinarith
    have hhigh : w < eta2 P ^ 2 := by
      by_contra hcon
      push Not at hcon
      have h1 : P.l * eta2 P ^ 2 = P.lamI * P.mu * (1 - P.l ^ 2) * eta2 P := by rw [← hη]; ring
      have h2 : 0 ≤ a * (P.lamI * P.mu * (1 - P.l ^ 2) * (eta2 P - P.p0)) := by
        have : 0 < eta2 P - P.p0 := by linarith
        positivity
      have := mul_nonneg hal.le (sub_nonneg.2 hcon)
      nlinarith [mul_pos hKp hc0]
    have hw0 : 0 ≤ w := by nlinarith
    have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw0
    have hu1 : P.p0 < Real.sqrt w := (Real.lt_sqrt hp0.le).2 hlow
    have hu2 : Real.sqrt w < eta2 P := (Real.sqrt_lt' (by linarith)).2 hhigh
    refine ⟨(1 - P.tau) * (Real.sqrt w - P.p0), ?_, ?_, ?_, ?_⟩
    · exact mul_pos hs (by linarith)
    · unfold d2; exact mul_lt_mul_of_pos_left (by linarith) hs
    · apply strictMonoOn_of_G P hP hp0 0 _ le_rfl
      intro d hd
      have hdp : 0 < d / (1 - P.tau) := div_pos hd.1 hs
      have hdlt : d / (1 - P.tau) < Real.sqrt w - P.p0 := by
        rw [div_lt_iff₀ hs]; have := hd.2; linarith
      have hu : price P d < Real.sqrt w := by rw [hprice]; linarith
      have hu0 : 0 < price P d := by rw [hprice]; linarith
      rw [hGf]
      have : price P d ^ 2 < w := by
        have := pow_lt_pow_left₀ hu hu0.le (two_ne_zero)
        rwa [hsq] at this
      exact mul_pos hal (by linarith)
    · apply strictAntiOn_of_G P hP hp0 _ _ (mul_pos hs (by linarith)).le
      intro d hd
      have hdgt : Real.sqrt w - P.p0 < d / (1 - P.tau) := by
        rw [lt_div_iff₀ hs]; have := hd.1; linarith
      have hu : Real.sqrt w < price P d := by rw [hprice]; linarith
      rw [hGf]
      have : w < price P d ^ 2 := by
        have := pow_lt_pow_left₀ hu (Real.sqrt_nonneg w) (two_ne_zero)
        rwa [hsq] at this
      exact mul_neg_of_pos_of_neg hal (by linarith)
