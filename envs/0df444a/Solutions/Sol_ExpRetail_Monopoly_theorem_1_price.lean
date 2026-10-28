-- Prove2me | solution 1 for ExpRetail.Monopoly.theorem_1_price
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:35:26.315882+00:00
-- url     : https://prove2.me/submissions/b1ad9fa6-980d-4341-ba53-07874a9c42e7

import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

noncomputable def er_GG (u0 cm c E F p : ℝ) : ℝ :=
  (Real.exp (u0 - p) * (1+F) * (p - cm) - c * (E + Real.exp (u0 - p) * F)) /
    ((1+E) + Real.exp (u0 - p) * (1+F))

noncomputable def er_HH (u0 cm c E F p : ℝ) : ℝ :=
  (1+E) * (1 - (p - cm)) + Real.exp (u0 - p) * (1+F) + c * (F - E) / (1+F)

lemma er_den_pos {E F : ℝ} (hE : 0 ≤ E) (hF : 0 ≤ F) (u0 p : ℝ) :
    0 < (1+E) + Real.exp (u0 - p) * (1+F) := by
  have := Real.exp_pos (u0 - p)
  positivity

lemma er_hasDerivAt_GG (u0 cm c E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (p : ℝ) :
    HasDerivAt (er_GG u0 cm c E F)
      (Real.exp (u0 - p) * (1+F) * er_HH u0 cm c E F p /
        ((1+E) + Real.exp (u0 - p) * (1+F))^2) p := by
  have ha : HasDerivAt (fun p => Real.exp (u0 - p)) (-Real.exp (u0 - p)) p := by
    have := ((hasDerivAt_id p).const_sub u0).exp
    simpa using this
  have hN : HasDerivAt (fun p => Real.exp (u0 - p) * (1+F) * (p - cm) - c * (E + Real.exp (u0 - p) * F))
      ((-Real.exp (u0 - p)) * (1+F) * (p - cm) + Real.exp (u0 - p) * (1+F) * 1
        - c * ((-Real.exp (u0 - p)) * F)) p := by
    have h1 := ((ha.mul_const (1+F)).mul ((hasDerivAt_id p).sub_const cm))
    have h2 := (((ha.mul_const F).const_add E).const_mul c)
    refine (h1.sub h2).congr_deriv ?_
    simp only [id]
  have hD : HasDerivAt (fun p => (1+E) + Real.exp (u0 - p) * (1+F)) ((-Real.exp (u0 - p)) * (1+F)) p := by
    simpa using (ha.mul_const (1+F)).const_add (1+E)
  have hpos := er_den_pos hE hF u0 p
  have := hN.div hD hpos.ne'
  unfold er_GG er_HH
  refine this.congr_deriv ?_
  have : (1 + F) ≠ 0 := by positivity
  field_simp
  ring


lemma er_HH_anti (u0 cm c E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    StrictAnti (er_HH u0 cm c E F) := by
  intro x y hxy
  unfold er_HH
  have h1 : Real.exp (u0 - y) < Real.exp (u0 - x) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : 0 < 1 + E := by linarith
  have h3 : 0 < 1 + F := by linarith
  have h4 := mul_lt_mul_of_pos_right h1 h3
  nlinarith

lemma er_HH_cont (u0 cm c E F : ℝ) : Continuous (er_HH u0 cm c E F) := by
  unfold er_HH
  fun_prop

lemma er_HH_root (u0 cm c E F : ℝ) (hE : 0 ≤ E) (hEF : E ≤ F) (hc : 0 ≤ c) :
    ∃ p0, er_HH u0 cm c E F p0 = 0 := by
  have hF : 0 ≤ F := le_trans hE hEF
  have h2 : 0 < 1 + E := by linarith
  have h3 : 0 < 1 + F := by linarith
  set a1 := Real.exp (u0 - (cm + 1)) with ha1
  have ha1p : 0 < a1 := Real.exp_pos _
  have hX : 0 ≤ c * (F - E) / (1 + F) := by
    apply div_nonneg (mul_nonneg hc (by linarith)) h3.le
  set X := a1 * (1 + F) + c * (F - E) / (1 + F) with hXdef
  have hXp : 0 ≤ X := by positivity
  set p2 := cm + 2 + X / (1 + E) with hp2
  have hX0 : 0 ≤ X / (1 + E) := div_nonneg hXp h2.le
  have hp1 : 0 < er_HH u0 cm c E F (cm + 1) := by
    unfold er_HH
    have : 0 < a1 * (1 + F) := by positivity
    simp only [← ha1]
    nlinarith
  have hp2' : er_HH u0 cm c E F p2 < 0 := by
    unfold er_HH
    have hle : Real.exp (u0 - p2) ≤ a1 := Real.exp_le_exp.mpr (by rw [hp2]; linarith)
    have := mul_le_mul_of_nonneg_right hle h3.le
    have e : (1 + E) * (X / (1 + E)) = X := by field_simp
    have e2 : (1 + E) * (1 - (p2 - cm)) = -(1+E) - X := by
      rw [hp2]; nlinarith [e]
    rw [e2]
    simp only [hXdef] at *
    linarith
  have hle : cm + 1 ≤ p2 := by rw [hp2]; linarith
  have := intermediate_value_Icc' hle (er_HH_cont u0 cm c E F).continuousOn
  obtain ⟨p0, _, hp0⟩ := this ⟨hp2'.le, hp1.le⟩
  exact ⟨p0, hp0⟩

lemma er_GG_max (u0 cm c E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (p0 : ℝ)
    (h0 : er_HH u0 cm c E F p0 = 0) (p : ℝ) : er_GG u0 cm c E F p ≤ er_GG u0 cm c E F p0 := by
  have hanti := er_HH_anti u0 cm c E F hE hF
  have hd := er_hasDerivAt_GG u0 cm c E F hE hF
  have hcont : Continuous (er_GG u0 cm c E F) :=
    continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hdiff : Differentiable ℝ (er_GG u0 cm c E F) := fun x => (hd x).differentiableAt
  rcases le_total p p0 with h | h
  · have hm : MonotoneOn (er_GG u0 cm c E F) (Set.Iic p0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic p0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(hd x).deriv]
      have : 0 ≤ er_HH u0 cm c E F x := by
        have := hanti hx
        linarith
      have hpos := er_den_pos hE hF u0 x
      have := Real.exp_pos (u0 - x)
      positivity
    exact hm h (Set.mem_Iic.mpr le_rfl) h
  · have hm : AntitoneOn (er_GG u0 cm c E F) (Set.Ici p0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici p0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have hHx : er_HH u0 cm c E F x ≤ 0 := by
        have := hanti hx
        linarith
      have hpos := er_den_pos hE hF u0 x
      have hex := Real.exp_pos (u0 - x)
      have h1 : 0 < Real.exp (u0 - x) * (1 + F) := by positivity
      apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1.le hHx) (by positivity)
    exact hm (Set.mem_Ici.mpr le_rfl) h h

lemma er_root_of_max (u0 cm c E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (p0 : ℝ)
    (h : ∀ p, er_GG u0 cm c E F p ≤ er_GG u0 cm c E F p0) : er_HH u0 cm c E F p0 = 0 := by
  have hd := er_hasDerivAt_GG u0 cm c E F hE hF p0
  have hl : IsLocalMax (er_GG u0 cm c E F) p0 := Filter.Eventually.of_forall h
  have := hl.hasDerivAt_eq_zero hd
  have hpos := er_den_pos hE hF u0 p0
  have h1 : 0 < Real.exp (u0 - p0) * (1 + F) := by
    have := Real.exp_pos (u0 - p0); positivity
  rw [div_eq_zero_iff] at this
  rcases this with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 h1.ne'
    · exact h3
  · exact absurd h2 (by positivity)

lemma er_rel (u0 cm c E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (p0 : ℝ)
    (h0 : er_HH u0 cm c E F p0 = 0) :
    Real.exp (u0 - p0) * (1 + F) = er_GG u0 cm c E F p0 * (1 + E) + c * E := by
  have h3 : 0 < 1 + F := by linarith
  have hpos := er_den_pos hE hF u0 p0
  unfold er_HH at h0
  unfold er_GG
  have hH' : (1+E) * (1 - (p0 - cm)) * (1+F) + Real.exp (u0 - p0) * (1+F) * (1+F) + c * (F - E) = 0 := by
    have : (1+F) * ((1+E) * (1 - (p0 - cm)) + Real.exp (u0 - p0) * (1+F) + c * (F - E) / (1+F)) = 0 := by
      rw [h0]; ring
    field_simp at this
    linarith
  field_simp
  linear_combination (Real.exp (u0 - p0)) * hH'


noncomputable def er_E (P : Params) (u : ℝ) : ℝ := Real.exp (u - P.t)
noncomputable def er_F (P : Params) (u : ℝ) : ℝ := Real.exp (u + synergy P u)
noncomputable def er_c (P : Params) (u : ℝ) : ℝ := P.eta * u ^ 2

lemma er_Z_eq (P : Params) (u p : ℝ) :
    partitionSum P u p =
      (1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u) := by
  have h00 : Real.exp (mu P u p 0 0) = 1 := by simp [mu]
  have h01 : Real.exp (mu P u p 0 1) = Real.exp (P.um - P.t - p) := by
    simp [mu, vm]
  have h10 : Real.exp (mu P u p 1 0) = er_E P u := by
    simp [mu, vx, er_E]
  have h11 : Real.exp (mu P u p 1 1) = er_F P u * Real.exp (P.um - P.t - p) := by
    unfold er_F
    rw [← Real.exp_add]
    congr 1
    simp [mu, vx, vm, psi]
    ring
  unfold partitionSum
  simp only [Fin.sum_univ_two]
  rw [h00, h01, h10, h11]
  ring

lemma er_profit_eq (P : Params) (u p : ℝ) :
    profit P u p = er_GG (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) p := by
  have h01 : Real.exp (mu P u p 0 1) = Real.exp (P.um - P.t - p) := by
    simp [mu, vm]
  have h10 : Real.exp (mu P u p 1 0) = er_E P u := by
    simp [mu, vx, er_E]
  have h11 : Real.exp (mu P u p 1 1) = er_F P u * Real.exp (P.um - P.t - p) := by
    unfold er_F
    rw [← Real.exp_add]
    congr 1
    simp [mu, vx, vm, psi]
    ring
  have hZ := er_Z_eq P u p
  have hpos : 0 < (1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u) := by
    unfold er_E er_F
    have := Real.exp_pos (u - P.t)
    have := Real.exp_pos (u + synergy P u)
    have := Real.exp_pos (P.um - P.t - p)
    positivity
  unfold profit basketProb expCost er_GG er_c
  rw [hZ, h01, h10, h11]
  field_simp

lemma er_profitN_eq (P : Params) (p : ℝ) :
    profitN P p = er_GG (P.um - P.t) P.cm 0 0 0 p := by
  unfold profitN q1N er_GG vm
  have := Real.exp_pos (P.um - P.t - p)
  field_simp
  ring

lemma er_CS_eq (P : Params) (u p : ℝ) :
    CS P u p = Real.log ((1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u)) := by
  unfold CS; rw [er_Z_eq]

lemma er_CSN_eq (P : Params) (p : ℝ) :
    CSN P p = Real.log (1 + Real.exp (P.um - P.t - p)) := by
  unfold CSN vm; rfl


lemma er_syn_nonneg (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ synergy P u := by
  obtain ⟨_, _, hs, hl⟩ := hP
  unfold synergy
  have : Real.exp (-(P.lam * u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  exact mul_nonneg hs.le (by linarith)

lemma er_syn_le (P : Params) (hP : P.Standing) (u : ℝ) : synergy P u ≤ P.s := by
  obtain ⟨_, _, hs, hl⟩ := hP
  unfold synergy
  have := Real.exp_pos (-(P.lam * u))
  nlinarith

lemma er_E_pos (P : Params) (u : ℝ) : 0 < er_E P u := Real.exp_pos _
lemma er_F_pos (P : Params) (u : ℝ) : 0 < er_F P u := Real.exp_pos _

lemma er_E_lt_F (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) : er_E P u < er_F P u := by
  unfold er_E er_F
  apply Real.exp_lt_exp.mpr
  have := er_syn_nonneg P hP hu
  have := hP.1
  linarith

lemma er_c_nonneg (P : Params) (hP : P.Standing) (u : ℝ) : 0 ≤ er_c P u := by
  unfold er_c; have := hP.2.1; positivity

lemma er_optN_iff (P : Params) (p : ℝ) :
    IsOptPriceN P p ↔ er_HH (P.um - P.t) P.cm 0 0 0 p = 0 := by
  constructor
  · intro h
    apply er_root_of_max _ _ _ _ _ le_rfl le_rfl
    intro p'
    have := h p'
    rwa [er_profitN_eq, er_profitN_eq] at this
  · intro h p'
    rw [er_profitN_eq, er_profitN_eq]
    exact er_GG_max _ _ _ _ _ le_rfl le_rfl p h p'

lemma er_opt_iff (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) (p : ℝ) :
    IsOptPrice P u p ↔
      er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) p = 0 := by
  have hE := (er_E_pos P u).le
  have hF := (er_F_pos P u).le
  constructor
  · intro h
    apply er_root_of_max _ _ _ _ _ hE hF
    intro p'
    have := h p'
    rwa [er_profit_eq, er_profit_eq] at this
  · intro h p'
    rw [er_profit_eq, er_profit_eq]
    exact er_GG_max _ _ _ _ _ hE hF p h p'

lemma er_exists_optN (P : Params) : ∃ p, IsOptPriceN P p := by
  obtain ⟨p, hp⟩ := er_HH_root (P.um - P.t) P.cm 0 0 0 le_rfl le_rfl le_rfl
  exact ⟨p, (er_optN_iff P p).mpr hp⟩

lemma er_exists_opt (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) : ∃ p, IsOptPrice P u p := by
  obtain ⟨p, hp⟩ := er_HH_root (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u)
    (er_E_pos P u).le (er_E_lt_F P hP hu).le (er_c_nonneg P hP u)
  exact ⟨p, (er_opt_iff P hP hu p).mpr hp⟩

lemma er_optProfitN_eq (P : Params) {p : ℝ} (hp : IsOptPriceN P p) : optProfitN P = profitN P p := by
  unfold optProfitN
  apply IsGreatest.csSup_eq
  refine ⟨⟨p, rfl⟩, ?_⟩
  rintro _ ⟨p', rfl⟩
  exact hp p'

lemma er_optProfit_eq (P : Params) {u p : ℝ} (hp : IsOptPrice P u p) : optProfit P u = profit P u p := by
  unfold optProfit
  apply IsGreatest.csSup_eq
  refine ⟨⟨p, rfl⟩, ?_⟩
  rintro _ ⟨p', rfl⟩
  exact hp p'

lemma er_price_lt (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) {p pN : ℝ}
    (hp : IsOptPrice P u p) (hpN : IsOptPriceN P pN) : pN < p := by
  have h1 := (er_opt_iff P hP hu p).mp hp
  have h2 := (er_optN_iff P pN).mp hpN
  have hlt := er_E_lt_F P hP hu
  have hE := er_E_pos P u
  have hc := er_c_nonneg P hP u
  by_contra hcon
  have hcon := not_lt.mp hcon
  have hanti := er_HH_anti (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) hE.le (er_F_pos P u).le
  have h3 : er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) pN ≤
      er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) p := by
    rcases hcon.lt_or_eq with h | h
    · exact (hanti h).le
    · rw [h]
  have h4 : 0 < er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) pN := by
    unfold er_HH at h2 ⊢
    have hF1 : 0 < 1 + er_F P u := by have := er_F_pos P u; linarith
    have ha := Real.exp_pos (P.um - P.t - pN)
    have hX : 0 ≤ er_c P u * (er_F P u - er_E P u) / (1 + er_F P u) :=
      div_nonneg (mul_nonneg hc (by linarith)) hF1.le
    have h2' : 1 - (pN - P.cm) = -Real.exp (P.um - P.t - pN) := by linarith
    rw [h2']
    nlinarith [mul_pos ha (sub_pos.mpr hlt)]
  linarith

end ExpRetail.Monopoly

open ExpRetail.Monopoly

theorem solution (P : Params) (hP : P.Standing) :
    (∃ pN : ℝ, IsOptPriceN P pN) ∧
    (∀ pN : ℝ, IsOptPriceN P pN → optProfitN P = profitN P pN) ∧
    ∀ ux : ℝ, 0 ≤ ux →
      (∃ p : ℝ, IsOptPrice P ux p) ∧
      (∀ p : ℝ, IsOptPrice P ux p → optProfit P ux = profit P ux p) ∧
      ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN → pN < p := by
  refine ⟨er_exists_optN P, fun pN h => er_optProfitN_eq P h, fun ux hux => ⟨er_exists_opt P hP hux, fun p h => er_optProfit_eq P h, fun p pN h hN => er_price_lt P hP hux h hN⟩⟩
