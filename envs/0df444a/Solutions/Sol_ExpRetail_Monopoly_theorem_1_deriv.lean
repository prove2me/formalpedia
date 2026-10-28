-- Prove2me | solution 1 for ExpRetail.Monopoly.theorem_1_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:43:40.58677+00:00
-- url     : https://prove2.me/submissions/063ab9e5-9421-4d8d-8823-ab15bad33524

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


lemma er_GG_upper (u0 cm c E F M : ℝ) (hE : 0 < E) (hEF : E ≤ F) (hc : 0 ≤ c) (hM : 1 ≤ M)
    (hFM : F ≤ E * M) (p : ℝ) :
    er_GG u0 cm c E F p ≤ M * Real.exp (u0 - cm) - c * (E / (1 + E)) := by
  have hF : 0 < F := lt_of_lt_of_le hE hEF
  have ha := Real.exp_pos (u0 - p)
  set a := Real.exp (u0 - p) with hadef
  have hD : 0 < (1 + E) + a * (1 + F) := by positivity
  have hrev : a * (1 + F) * (p - cm) / ((1 + E) + a * (1 + F)) ≤ M * Real.exp (u0 - cm) := by
    have hK : 0 ≤ M * Real.exp (u0 - cm) := by positivity
    by_cases hm : p - cm ≤ 0
    · have : a * (1 + F) * (p - cm) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hm
      calc _ ≤ (0:ℝ) := div_nonpos_of_nonpos_of_nonneg this hD.le
        _ ≤ _ := hK
    · push Not at hm
      have hBM : 1 + F ≤ M * ((1 + E) + a * (1 + F)) := by
        have : a * (1 + F) ≥ 0 := by positivity
        nlinarith
      have h1 : a * (1 + F) * (p - cm) / ((1 + E) + a * (1 + F)) ≤ M * (a * (p - cm)) := by
        rw [div_le_iff₀ hD]
        have h3 : 0 ≤ a * (p - cm) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hBM h3]
      have h2 : a * (p - cm) ≤ Real.exp (u0 - cm) := by
        have e1 : a = Real.exp (u0 - cm) * Real.exp (-(p - cm)) := by
          rw [hadef, ← Real.exp_add]; congr 1; ring
        have e2 : (p - cm) * Real.exp (-(p - cm)) ≤ 1 := by
          have := Real.add_one_le_exp (p - cm)
          have e3 : Real.exp (-(p - cm)) * Real.exp (p - cm) = 1 := by
            rw [← Real.exp_add]; simp
          have e4 := Real.exp_pos (-(p - cm))
          nlinarith
        rw [e1]
        have := Real.exp_pos (u0 - cm)
        nlinarith
      calc _ ≤ M * (a * (p - cm)) := h1
        _ ≤ M * Real.exp (u0 - cm) := by nlinarith
  have hcost : c * (E / (1 + E)) ≤ c * (E + a * F) / ((1 + E) + a * (1 + F)) := by
    rw [le_div_iff₀ hD]
    have h1 : E / (1 + E) * ((1 + E) + a * (1 + F)) ≤ E + a * F := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hEF)]
    calc c * (E / (1 + E)) * ((1 + E) + a * (1 + F)) = c * (E / (1 + E) * ((1 + E) + a * (1 + F))) := by ring
      _ ≤ c * (E + a * F) := mul_le_mul_of_nonneg_left h1 hc
  unfold er_GG
  rw [← hadef]
  have : (a * (1 + F) * (p - cm) - c * (E + a * F)) / ((1 + E) + a * (1 + F))
      = a * (1 + F) * (p - cm) / ((1 + E) + a * (1 + F)) - c * (E + a * F) / ((1 + E) + a * (1 + F)) := by
    rw [sub_div]
  rw [this]
  linarith


noncomputable def er_K (P : Params) : ℝ := Real.exp (P.t + P.s) * Real.exp (P.um - P.t - P.cm)

lemma er_profit_upper (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) (p : ℝ) :
    profit P u p ≤ er_K P - er_c P u * (er_E P u / (1 + er_E P u)) := by
  rw [er_profit_eq]
  have hM : 1 ≤ Real.exp (P.t + P.s) := by
    rw [Real.one_le_exp_iff]; have := hP.1; have := hP.2.2.1; linarith
  have hFM : er_F P u ≤ er_E P u * Real.exp (P.t + P.s) := by
    unfold er_F er_E
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := er_syn_le P hP u
    linarith
  exact er_GG_upper _ _ _ _ _ _ (er_E_pos P u) (er_E_lt_F P hP hu).le (er_c_nonneg P hP u) hM hFM p

lemma er_optProfit_upper (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) :
    optProfit P u ≤ er_K P - er_c P u * (er_E P u / (1 + er_E P u)) := by
  unfold optProfit
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p, rfl⟩
  exact er_profit_upper P hP hu p

lemma er_optProfitN_pos (P : Params) : 0 < optProfitN P := by
  obtain ⟨p, hp⟩ := er_exists_optN P
  rw [er_optProfitN_eq P hp, er_profitN_eq]
  have h := (er_optN_iff P p).mp hp
  unfold er_HH at h
  unfold er_GG
  have ha := Real.exp_pos (P.um - P.t - p)
  have hm : p - P.cm = 1 + Real.exp (P.um - P.t - p) := by linarith
  rw [hm]
  simp only [add_zero, zero_mul, mul_zero, sub_zero, zero_sub]
  positivity

lemma er_limit (P : Params) (hP : P.Standing) :
    Filter.Tendsto (optProfit P) Filter.atTop Filter.atBot := by
  have heta := hP.2.1
  have h1 : Filter.Tendsto (fun u : ℝ => P.eta / 2 * u ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (two_ne_zero)).const_mul_atTop (by positivity)
  have h2 : Filter.Tendsto (fun u : ℝ => er_K P - P.eta / 2 * u ^ 2) Filter.atTop Filter.atBot := by
    have := Filter.tendsto_atBot_add_const_left Filter.atTop (er_K P)
      (Filter.tendsto_neg_atTop_atBot.comp h1)
    simpa [sub_eq_add_neg] using this
  apply Filter.tendsto_atBot_mono' _ _ h2
  filter_upwards [Filter.eventually_ge_atTop (max P.t 0)] with u hu
  have hu0 : 0 ≤ u := le_trans (le_max_right _ _) hu
  have hut : P.t ≤ u := le_trans (le_max_left _ _) hu
  refine le_trans (er_optProfit_upper P hP hu0) ?_
  have hE1 : 1 ≤ er_E P u := by
    unfold er_E; rw [Real.one_le_exp_iff]; linarith
  have : 1 / 2 ≤ er_E P u / (1 + er_E P u) := by
    rw [div_eq_mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by linarith)]; linarith
  unfold er_c
  nlinarith [mul_nonneg heta.le (sq_nonneg u), mul_le_mul_of_nonneg_left this (mul_nonneg heta.le (sq_nonneg u))]


open Filter Topology Set

lemma er_envelope (f : ℝ → ℝ → ℝ) (fu : ℝ → ℝ → ℝ) (pS : ℝ → ℝ)
    (hfu : ∀ u p, HasDerivAt (fun u => f u p) (fu u p) u)
    (hc : ContinuousAt (fun x : ℝ × ℝ => fu x.1 x.2) (0, pS 0))
    (hmax : ∀ u, 0 ≤ u → ∀ p, f u p ≤ f u (pS u))
    (hp : ∀ ε > 0, ∃ δ > 0, ∀ u, 0 ≤ u → u < δ → |pS u - pS 0| < ε) :
    HasDerivWithinAt (fun u => f u (pS u)) (fu 0 (pS 0)) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  -- lower bound
  have hlow := (hasDerivAt_iff_tendsto_slope.mp (hfu 0 (pS 0)))
  rw [Metric.tendsto_nhdsWithin_nhds] at hlow
  obtain ⟨δ1, hδ1, h1⟩ := hlow (ε / 2) hε2
  -- continuity
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.mp hc (ε / 2) hε2
  obtain ⟨δ3, hδ3, h3⟩ := hp (δ2 / 2) (by positivity)
  refine ⟨min δ1 (min (δ2 / 2) δ3), by positivity, ?_⟩
  intro x hx hxd
  have hx0 : 0 < x := by
    obtain ⟨hx1, hx2⟩ := hx
    exact lt_of_le_of_ne hx1 (fun h => hx2 h.symm)
  rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hxd
  have hxd1 : x < δ1 := lt_of_lt_of_le hxd (min_le_left _ _)
  have hxd2 : x < δ2 / 2 := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _))
  have hxd3 : x < δ3 := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _))
  have hslope_eq : ∀ g : ℝ → ℝ, slope g 0 x = (g x - g 0) / x := by
    intro g; rw [slope_def_field]; simp
  -- lower
  have hL := h1 (x := x) (show x ∈ ({0}:Set ℝ)ᶜ from by simpa using hx0.ne') (by rw [Real.dist_eq, sub_zero, abs_of_pos hx0]; exact hxd1)
  rw [Real.dist_eq] at hL
  have hL' := (abs_lt.mp hL).1
  -- upper via MVT
  set q := pS x with hq
  have hmvt := exists_hasDerivAt_eq_slope (fun u => f u q) (fun u => fu u q) hx0
    (by
      apply HasDerivAt.continuousOn
      intro y _; exact hfu y q)
    (fun y _ => hfu y q)
  obtain ⟨ξ, hξ, hξe⟩ := hmvt
  have hdist : dist (ξ, q) (0, pS 0) < δ2 := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq, sub_zero, abs_of_pos hξ.1]; linarith [hξ.2]
    · rw [Real.dist_eq]
      have := h3 x hx0.le hxd3
      linarith
  have hU := h2 hdist
  rw [Real.dist_eq] at hU
  have hU' := (abs_lt.mp hU).2
  simp only at hU' hξe
  have hslopeg : slope (fun u => f u (pS u)) 0 x = (f x q - f 0 (pS 0)) / x := by
    rw [hslope_eq]
  have hslopef : slope (fun u => f u (pS 0)) 0 x = (f x (pS 0) - f 0 (pS 0)) / x := hslope_eq _
  have hge : (f x (pS 0) - f 0 (pS 0)) / x ≤ (f x q - f 0 (pS 0)) / x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith [hmax x hx0.le (pS 0)]
  have hle : (f x q - f 0 (pS 0)) / x ≤ (f x q - f 0 q) / x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith [hmax 0 le_rfl q]
  have hmv : fu ξ q = (f x q - f 0 q) / x := by rw [hξe]; simp
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


lemma er_hasDerivAt_u (a m : ℝ) (E F c : ℝ → ℝ) (E' F' c' u : ℝ)
    (hE : HasDerivAt E E' u) (hF : HasDerivAt F F' u) (hc : HasDerivAt c c' u)
    (hD : (1 + E u) + a * (1 + F u) ≠ 0) :
    HasDerivAt (fun u => (a * (1 + F u) * m - c u * (E u + a * F u)) / ((1 + E u) + a * (1 + F u)))
      (((a * F' * m - c' * (E u + a * F u) - c u * (E' + a * F')) * ((1 + E u) + a * (1 + F u))
        - (a * (1 + F u) * m - c u * (E u + a * F u)) * (E' + a * F')) /
        ((1 + E u) + a * (1 + F u)) ^ 2) u := by
  have hN : HasDerivAt (fun u => a * (1 + F u) * m - c u * (E u + a * F u))
      (a * F' * m - c' * (E u + a * F u) - c u * (E' + a * F')) u := by
    have h1 := ((hF.const_add 1).const_mul a).mul_const m
    have h2 := hc.mul (hE.add (hF.const_mul a))
    refine (h1.sub h2).congr_deriv ?_
    simp only [Pi.add_apply]
    ring
  have hD' : HasDerivAt (fun u => (1 + E u) + a * (1 + F u)) (E' + a * F') u := by
    have := (hE.const_add 1).add ((hF.const_add 1).const_mul a)
    refine this.congr_deriv ?_
    ring
  exact hN.div hD' hD

noncomputable def er_dF (P : Params) (u : ℝ) : ℝ :=
  er_F P u * (1 + P.s * (P.lam * Real.exp (-(P.lam * u))))

noncomputable def er_fu (P : Params) (u p : ℝ) : ℝ :=
  ((Real.exp (P.um - P.t - p) * er_dF P u * (p - P.cm) - (2 * P.eta * u) * (er_E P u + Real.exp (P.um - P.t - p) * er_F P u)
      - er_c P u * (er_E P u + Real.exp (P.um - P.t - p) * er_dF P u)) *
      ((1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u))
    - (Real.exp (P.um - P.t - p) * (1 + er_F P u) * (p - P.cm) - er_c P u * (er_E P u + Real.exp (P.um - P.t - p) * er_F P u))
        * (er_E P u + Real.exp (P.um - P.t - p) * er_dF P u)) /
    ((1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u)) ^ 2

lemma er_hasDerivAt_profit_u (P : Params) (p u : ℝ) :
    HasDerivAt (fun u => profit P u p) (er_fu P u p) u := by
  have hE : HasDerivAt (er_E P) (er_E P u) u := by
    have h := ((hasDerivAt_id u).sub_const P.t).exp
    simp only [id, mul_one] at h
    exact h
  have hF : HasDerivAt (er_F P) (er_dF P u) u := by
    have h1 : HasDerivAt (fun u => synergy P u) (P.s * (P.lam * Real.exp (-(P.lam * u)))) u := by
      have := ((((hasDerivAt_id u).const_mul P.lam).neg).exp)
      have h2 := (this.const_sub 1).const_mul P.s
      unfold synergy
      refine h2.congr_deriv ?_
      simp only [Pi.neg_apply, id]
      ring
    have := ((hasDerivAt_id u).add h1).exp
    refine this.congr_deriv ?_
    unfold er_dF er_F
    simp only [Pi.add_apply, id]
  have hc : HasDerivAt (er_c P) (2 * P.eta * u) u := by
    have := ((hasDerivAt_id u).pow 2).const_mul P.eta
    unfold er_c
    refine this.congr_deriv ?_
    simp
    ring
  have hD : (1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u) ≠ 0 :=
    (er_den_pos (er_E_pos P u).le (er_F_pos P u).le _ _).ne'
  have := er_hasDerivAt_u (Real.exp (P.um - P.t - p)) (p - P.cm) (er_E P) (er_F P) (er_c P)
    (er_E P u) (er_dF P u) (2 * P.eta * u) u hE hF hc hD
  have hfun : (fun u => profit P u p) = fun u => (Real.exp (P.um - P.t - p) * (1 + er_F P u) * (p - P.cm)
      - er_c P u * (er_E P u + Real.exp (P.um - P.t - p) * er_F P u)) /
        ((1 + er_E P u) + Real.exp (P.um - P.t - p) * (1 + er_F P u)) := by
    funext u
    rw [er_profit_eq]; unfold er_GG
    congr 3 <;> simp [sub_eq_add_neg, add_assoc]
  rw [hfun]
  exact this

lemma er_continuous_fu (P : Params) : Continuous (fun x : ℝ × ℝ => er_fu P x.1 x.2) := by
  unfold er_fu
  refine Continuous.div ?_ ?_ (fun x => ?_)
  · unfold er_dF er_c er_E er_F synergy; fun_prop
  · unfold er_E er_F synergy; fun_prop
  · exact (pow_pos (er_den_pos (er_E_pos P x.1).le (er_F_pos P x.1).le _ _) 2).ne'


noncomputable def er_pS (P : Params) (hP : P.Standing) (u : ℝ) : ℝ :=
  if h : 0 ≤ u then Classical.choose (er_exists_opt P hP h) else 0

lemma er_pS_opt (P : Params) (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) :
    IsOptPrice P u (er_pS P hP u) := by
  unfold er_pS
  rw [dif_pos hu]
  exact Classical.choose_spec (er_exists_opt P hP hu)

lemma er_pS_cont (P : Params) (hP : P.Standing) :
    ∀ ε > 0, ∃ δ > 0, ∀ u, 0 ≤ u → u < δ → |er_pS P hP u - er_pS P hP 0| < ε := by
  intro ε hε
  set p0 := er_pS P hP 0 with hp0
  have h0 := (er_opt_iff P hP le_rfl p0).mp (er_pS_opt P hP le_rfl)
  have hanti0 := er_HH_anti (P.um - P.t) P.cm (er_c P 0) (er_E P 0) (er_F P 0)
    (er_E_pos P 0).le (er_F_pos P 0).le
  have hlo : 0 < er_HH (P.um - P.t) P.cm (er_c P 0) (er_E P 0) (er_F P 0) (p0 - ε) := by
    have := hanti0 (show p0 - ε < p0 by linarith); linarith
  have hhi : er_HH (P.um - P.t) P.cm (er_c P 0) (er_E P 0) (er_F P 0) (p0 + ε) < 0 := by
    have := hanti0 (show p0 < p0 + ε by linarith); linarith
  have hcl : Continuous (fun u => er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) (p0 - ε)) := by
    unfold er_HH er_c er_E er_F synergy; fun_prop (disch := (intro x; positivity))
  have hch : Continuous (fun u => er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) (p0 + ε)) := by
    unfold er_HH er_c er_E er_F synergy; fun_prop (disch := (intro x; positivity))
  have ev1 : ∀ᶠ u in nhds (0:ℝ), 0 < er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) (p0 - ε) :=
    hcl.continuousAt.eventually (lt_mem_nhds hlo)
  have ev2 : ∀ᶠ u in nhds (0:ℝ), er_HH (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u) (p0 + ε) < 0 :=
    hch.continuousAt.eventually (gt_mem_nhds hhi)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (ev1.and ev2)
  refine ⟨δ, hδ, fun u hu hud => ?_⟩
  have hd : dist u 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hu]; exact hud
  obtain ⟨h1, h2⟩ := hδ' hd
  have hu0 := (er_opt_iff P hP hu _).mp (er_pS_opt P hP hu)
  have hanti := er_HH_anti (P.um - P.t) P.cm (er_c P u) (er_E P u) (er_F P u)
    (er_E_pos P u).le (er_F_pos P u).le
  rw [abs_lt]
  constructor
  · by_contra hcon
    have hc2 : er_pS P hP u ≤ p0 - ε := by linarith [not_lt.mp hcon]
    rcases hc2.lt_or_eq with h | h
    · have := hanti h; linarith
    · rw [h] at hu0; linarith
  · by_contra hcon
    have hc2 : p0 + ε ≤ er_pS P hP u := by linarith [not_lt.mp hcon]
    rcases hc2.lt_or_eq with h | h
    · have := hanti h; linarith
    · rw [← h] at hu0; linarith

lemma er_fu_zero_pos (P : Params) (hP : P.Standing) :
    0 < er_fu P 0 (er_pS P hP 0) := by
  set p0 := er_pS P hP 0 with hp0
  have h0 := (er_opt_iff P hP le_rfl p0).mp (er_pS_opt P hP le_rfl)
  have hE : er_E P 0 = Real.exp (-P.t) := by simp [er_E]
  have hF : er_F P 0 = 1 := by simp [er_F, synergy]
  have hc : er_c P 0 = 0 := by simp [er_c]
  have hdF : er_dF P 0 = 1 + P.s * P.lam := by simp [er_dF, hF]
  obtain ⟨ht, heta, hs, hl⟩ := hP
  have ha := Real.exp_pos (P.um - P.t - p0)
  set a := Real.exp (P.um - P.t - p0) with hadef
  set E0 := Real.exp (-P.t) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  have hE0lt : E0 < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold er_HH at h0
  rw [hc, hE, hF] at h0
  have hm : 0 < p0 - P.cm := by
    have : (1 + E0) * (p0 - P.cm) = (1 + E0) + a * (1 + 1) := by
      simp at h0; linarith
    by_contra hcon
    have := not_lt.mp hcon
    nlinarith
  unfold er_fu
  rw [hc, hE, hF, hdF]
  simp only [mul_zero, zero_mul, sub_zero, zero_add, add_zero]
  apply div_pos _ (by positivity)
  have key : (a * (1 + P.s * P.lam) * (p0 - P.cm) * (1 + E0 + a * (1 + 1)) -
      a * (1 + 1) * (p0 - P.cm) * (E0 + a * (1 + P.s * P.lam))) =
      a * (p0 - P.cm) * ((1 + E0) + P.s * P.lam * (1 + E0) - 2 * E0) := by ring
  rw [key]
  have : 0 < (1 + E0) + P.s * P.lam * (1 + E0) - 2 * E0 := by
    nlinarith [mul_pos (mul_pos hs hl) (by linarith : (0:ℝ) < 1 + E0)]
  positivity

lemma er_deriv (P : Params) (hP : P.Standing) :
    ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt (optProfit P) d (Set.Ici 0) 0 := by
  refine ⟨er_fu P 0 (er_pS P hP 0), er_fu_zero_pos P hP, ?_⟩
  have h := er_envelope (profit P) (er_fu P) (er_pS P hP) (fun u p => er_hasDerivAt_profit_u P p u)
    ((er_continuous_fu P).continuousAt)
    (fun u hu p => er_pS_opt P hP hu p) (er_pS_cont P hP)
  refine h.congr (fun y hy => ?_) ?_
  · exact er_optProfit_eq P (er_pS_opt P hP hy)
  · exact er_optProfit_eq P (er_pS_opt P hP le_rfl)

end ExpRetail.Monopoly

open ExpRetail.Monopoly

theorem solution (P : Params) (hP : P.Standing) :
    ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt (optProfit P) d (Set.Ici 0) 0 :=
  er_deriv P hP
