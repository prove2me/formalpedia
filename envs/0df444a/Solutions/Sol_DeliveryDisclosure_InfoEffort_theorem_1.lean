-- Prove2me | solution 1 for DeliveryDisclosure.InfoEffort.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T11:53:59.768459+00:00
-- url     : https://prove2.me/submissions/d667ccde-3f84-44a2-9ae3-f111dd99dac4

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

set_option autoImplicit false

open DeliveryDisclosure.InfoEffort Real Set

namespace DD4690

lemma omega_pos (P : Params) (hY : 0 < P.ωY) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) :
    0 < ωθ P ϕ := by
  unfold ωθ
  apply Real.sqrt_pos.2
  have h3 : 0 ≤ 1 - ϕ ^ 2 := by nlinarith
  have h2 : 0 < P.ωY ^ 2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg P.βr) h3]

lemma sigmoid_le_exp (x : ℝ) : sigmoid x ≤ exp x := by
  rw [Real.sigmoid_def]
  have h1 : 0 < exp (-x) := exp_pos _
  have : exp x = (exp (-x))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [this]; exact inv_anti₀ h1 (by linarith)

lemma Vdet_anti (P : Params) (hρ : 0 ≤ P.βr * P.ρ) {p t : ℝ} (ht : 0 ≤ t) {l1 l2 : ℝ}
    (h : l1 ≤ l2) : Vdet P p t l2 ≤ Vdet P p t l1 := by
  unfold Vdet
  have : Real.exp (-(P.μ - l1) * t) ≤ Real.exp (-(P.μ - l2) * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left this hρ]

lemma dem_eq_of_fix (P : Params) (hΛ : 0 < P.Λ) (hρ : 0 ≤ P.βr * P.ρ) {p t ϕ : ℝ}
    (hω : 0 < ωθ P ϕ) (ht : 0 ≤ t) {l : ℝ} (hl0 : 0 ≤ l) (hlΛ : l ≤ P.Λ)
    (hfix : l = P.Λ * sigmoid ((Vdet P p t l - P.Ve) / ωθ P ϕ)) : dem P p t ϕ = l := by
  unfold dem
  apply IsGreatest.csSup_eq
  refine ⟨⟨⟨hl0, hlΛ⟩, hfix.le⟩, ?_⟩
  rintro x ⟨⟨hx0, hxΛ⟩, hx⟩
  by_contra hlt
  push Not at hlt
  have hV := Vdet_anti P hρ (p := p) ht hlt.le
  have hs : sigmoid ((Vdet P p t x - P.Ve) / ωθ P ϕ) ≤ sigmoid ((Vdet P p t l - P.Ve) / ωθ P ϕ) :=
    Real.sigmoid_le (div_le_div_of_nonneg_right (by linarith) hω.le)
  have := mul_le_mul_of_nonneg_left hs hΛ.le
  linarith

lemma dem_fix (P : Params) (hΛ : 0 < P.Λ) (hρ : 0 ≤ P.βr * P.ρ) {p t ϕ : ℝ}
    (hω : 0 < ωθ P ϕ) (ht : 0 ≤ t) :
    0 < dem P p t ϕ ∧ dem P p t ϕ < P.Λ ∧
      dem P p t ϕ = P.Λ * sigmoid ((Vdet P p t (dem P p t ϕ) - P.Ve) / ωθ P ϕ) := by
  set f : ℝ → ℝ := fun l => P.Λ * sigmoid ((Vdet P p t l - P.Ve) / ωθ P ϕ) - l with hf
  have hcont : ContinuousOn f (Icc 0 P.Λ) := by
    apply Continuous.continuousOn
    simp only [hf, Vdet]
    fun_prop
  have hf0 : 0 ≤ f 0 := by
    simp only [hf]; have := Real.sigmoid_pos ((Vdet P p t 0 - P.Ve) / ωθ P ϕ); nlinarith
  have hfΛ : f P.Λ ≤ 0 := by
    simp only [hf]; have := Real.sigmoid_lt_one ((Vdet P p t P.Λ - P.Ve) / ωθ P ϕ); nlinarith
  obtain ⟨l, ⟨hl0, hlΛ⟩, hfl⟩ := intermediate_value_Icc' hΛ.le hcont ⟨hfΛ, hf0⟩
  have hfix : l = P.Λ * sigmoid ((Vdet P p t l - P.Ve) / ωθ P ϕ) := by
    simp only [hf] at hfl; linarith
  have hd := dem_eq_of_fix P hΛ hρ hω ht hl0 hlΛ hfix
  rw [hd]
  refine ⟨?_, ?_, hfix⟩
  · rw [hfix]; exact mul_pos hΛ (Real.sigmoid_pos _)
  · rw [hfix]; have := Real.sigmoid_lt_one ((Vdet P p t l - P.Ve) / ωθ P ϕ); nlinarith

lemma Vdet_le_Vbar (P : Params) (hρ : 0 ≤ P.βr * P.ρ) (hβt : 0 < P.βt) {p t l : ℝ}
    (hp : P.c ≤ p) (ht : 0 ≤ t) : Vdet P p t l ≤ Vbar P := by
  unfold Vdet Vbar
  have := exp_pos (-(P.μ - l) * t)
  nlinarith [mul_nonneg hρ this.le, mul_nonneg hβt.le ht]

lemma dem_le_Sbar (P : Params) (hP : Standing P) {p t ϕ : ℝ} (hω : 0 < ωθ P ϕ)
    (hp : P.c ≤ p) (ht : 0 ≤ t) : dem P p t ϕ ≤ Sbar P ϕ * P.Λ := by
  obtain ⟨hΛ, hβr, hβt, hρ, -, -, -, -⟩ := hP
  have hρ' : 0 ≤ P.βr * P.ρ := by positivity
  obtain ⟨-, -, hfix⟩ := dem_fix P hΛ hρ' (p := p) hω ht
  rw [hfix, mul_comm]
  unfold Sbar
  apply mul_le_mul_of_nonneg_right _ hΛ.le
  apply Real.sigmoid_le
  apply div_le_div_of_nonneg_right _ hω.le
  linarith [Vdet_le_Vbar P hρ' hβt (l := dem P p t ϕ) hp ht]

/-- the capacity margin κ = βt e/(βr ρ) -/
noncomputable def kap (P : Params) : ℝ := P.βt / (P.βr * P.ρ) * Real.exp 1

lemma kap_pos (P : Params) (hP : Standing P) : 0 < kap P := by
  obtain ⟨-, hβr, hβt, hρ, -⟩ := hP
  unfold kap; positivity

lemma cap_margin (P : Params) (hP : Standing P) {p t ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1)
    (hp : P.c ≤ p) (ht : 0 ≤ t) : kap P ≤ P.μ - dem P p t ϕ := by
  have hω := omega_pos P hP.2.2.2.2.1 h0 h1
  have h := dem_le_Sbar P hP hω hp ht
  have hc := hP.2.2.2.2.2.2.2 ϕ ⟨h0, h1⟩
  unfold kap; linarith

lemma nonneg_plan (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) :
    Feasible P ϕ (P.c + P.b, 1 / kap P) ∧ 0 ≤ profit P (P.c + P.b) (1 / kap P) ϕ := by
  have hk := kap_pos P hP
  have hb := hP.2.2.2.2.2.2.1
  have ht : (0 : ℝ) ≤ 1 / kap P := by positivity
  have hm := cap_margin P hP h0 h1 (p := P.c + P.b) (by linarith) ht
  have hω := omega_pos P hP.2.2.2.2.1 h0 h1
  have hd := (dem_fix P hP.1 (by have := hP.2.1; have := hP.2.2.2.1; positivity)
    (p := P.c + P.b) hω ht).1
  refine ⟨⟨by simp; linarith, ht, ?_⟩, ?_⟩
  · simp only
    rw [mul_one_div, le_div_iff₀ hk]; linarith
  · unfold profit
    apply mul_nonneg hd.le; nlinarith

lemma profit_bdd (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) :
    BddAbove ((fun x : ℝ × ℝ => profit P x.1 x.2 ϕ) '' {x | Feasible P ϕ x}) := by
  obtain ⟨hΛ, hβr, hβt, hρ, hY, hc, hb, -⟩ := hP
  have hω := omega_pos P hY h0 h1
  have hρ' : 0 ≤ P.βr * P.ρ := by positivity
  set ω := ωθ P ϕ with hωdef
  set A := P.α + P.βr * P.ρ - P.Ve with hA
  refine ⟨P.Λ * exp (A / ω) * ω, ?_⟩
  rintro _ ⟨⟨p, t⟩, ⟨hp, ht, -⟩, rfl⟩
  simp only at hp ht ⊢
  obtain ⟨hl0, -, hfix⟩ := dem_fix P hΛ hρ' (p := p) hω ht
  set l := dem P p t ϕ with hl
  have hEpos : 0 < P.Λ * exp (A / ω) * ω := by positivity
  unfold profit
  rw [← hl]
  by_cases hm : p - P.b * ϕ - P.c ≤ 0
  · nlinarith
  push Not at hm
  have hV : Vdet P p t l - P.Ve ≤ A - p := by
    unfold Vdet; rw [hA]
    have := exp_pos (-(P.μ - l) * t)
    nlinarith [mul_nonneg hρ' this.le, mul_nonneg hβt.le ht]
  have hσ : sigmoid ((Vdet P p t l - P.Ve) / ω) ≤ exp (A / ω) * exp (-(p / ω)) := by
    rw [← exp_add]
    refine (sigmoid_le_exp _).trans (exp_le_exp.2 ?_)
    have : A / ω + -(p / ω) = (A - p) / ω := by ring
    rw [this]; exact div_le_div_of_nonneg_right hV hω.le
  have hxe : (p / ω) * exp (-(p / ω)) ≤ 1 := by
    have h1 := Real.add_one_le_exp (p / ω)
    have h2 : exp (p / ω) * exp (-(p / ω)) = 1 := by rw [← exp_add]; simp
    have h3 := exp_pos (-(p / ω))
    nlinarith
  have hpe : p * exp (-(p / ω)) ≤ ω := by
    have : p * exp (-(p / ω)) = ω * ((p / ω) * exp (-(p / ω))) := by field_simp
    rw [this]; nlinarith
  have hmarg : p - P.b * ϕ - P.c ≤ p := by nlinarith
  have hlb : l ≤ P.Λ * (exp (A / ω) * exp (-(p / ω))) := by
    rw [hfix]; exact mul_le_mul_of_nonneg_left hσ hΛ.le
  calc l * (p - P.b * ϕ - P.c) ≤ l * p := mul_le_mul_of_nonneg_left hmarg hl0.le
    _ ≤ P.Λ * (exp (A / ω) * exp (-(p / ω))) * p :=
        mul_le_mul_of_nonneg_right hlb (by linarith)
    _ = P.Λ * exp (A / ω) * (p * exp (-(p / ω))) := by ring
    _ ≤ P.Λ * exp (A / ω) * ω := mul_le_mul_of_nonneg_left hpe (by positivity)

lemma optProfit_nonneg (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) :
    0 ≤ optProfit P ϕ := by
  obtain ⟨hf, hpos⟩ := nonneg_plan P hP h0 h1
  exact hpos.trans (le_csSup (profit_bdd P hP h0 h1) ⟨_, hf, rfl⟩)

lemma le_optProfit (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1)
    {p t : ℝ} (hf : Feasible P ϕ (p, t)) : profit P p t ϕ ≤ optProfit P ϕ :=
  le_csSup (profit_bdd P hP h0 h1) ⟨(p, t), hf, rfl⟩

/-- The demand index D = (V - Ve)/ω of a plan (the logit of the market share). -/
noncomputable def idx (P : Params) (p t ϕ : ℝ) : ℝ :=
  (Vdet P p t (dem P p t ϕ) - P.Ve) / ωθ P ϕ

/-- TRANSPORT: keep the demand and delivery time, move the price. -/
lemma transport (P : Params) (hP : Standing P) {ϕ1 ϕ2 p t : ℝ} (h1 : ϕ1 ∈ Icc (0:ℝ) 1)
    (h2 : ϕ2 ∈ Icc (0:ℝ) 1) (hf : Feasible P ϕ1 (p, t)) :
    profit P p t ϕ1 + dem P p t ϕ1 * ((ωθ P ϕ1 - ωθ P ϕ2) * idx P p t ϕ1 - P.b * (ϕ2 - ϕ1))
      ≤ optProfit P ϕ2 := by
  obtain ⟨hp, ht, hcap⟩ := hf
  simp only at hp ht hcap
  have hΛ := hP.1
  have hρ' : 0 ≤ P.βr * P.ρ := by have := hP.2.1; have := hP.2.2.2.1; positivity
  have hω1 := omega_pos P hP.2.2.2.2.1 h1.1 h1.2
  have hω2 := omega_pos P hP.2.2.2.2.1 h2.1 h2.2
  obtain ⟨hl0, hlΛ, hfix⟩ := dem_fix P hΛ hρ' (p := p) hω1 ht
  set l := dem P p t ϕ1 with hl
  set D := idx P p t ϕ1 with hD
  set p2 := p + (ωθ P ϕ1 - ωθ P ϕ2) * D with hp2
  have hV2 : Vdet P p2 t l - P.Ve = ωθ P ϕ2 * D := by
    have e1 : Vdet P p2 t l = Vdet P p t l - (ωθ P ϕ1 - ωθ P ϕ2) * D := by
      unfold Vdet; rw [hp2]; ring
    have e2 : Vdet P p t l - P.Ve = ωθ P ϕ1 * D := by
      rw [hD, idx, ← hl]; field_simp
    rw [e1]; linarith
  have hfix2 : l = P.Λ * sigmoid ((Vdet P p2 t l - P.Ve) / ωθ P ϕ2) := by
    rw [hV2, mul_div_cancel_left₀ _ hω2.ne', hD, idx, ← hl]; exact hfix
  have hd2 : dem P p2 t ϕ2 = l := dem_eq_of_fix P hΛ hρ' hω2 ht hl0.le hlΛ.le hfix2
  have hval : profit P p2 t ϕ2 =
      profit P p t ϕ1 + l * ((ωθ P ϕ1 - ωθ P ϕ2) * D - P.b * (ϕ2 - ϕ1)) := by
    unfold profit; rw [hd2, ← hl, hp2]; ring
  rw [← hval]
  by_cases hc2 : P.c ≤ p2
  · apply le_optProfit P hP h2.1 h2.2
    refine ⟨hc2, ht, ?_⟩
    simp only; rw [hd2]; exact hcap
  · push Not at hc2
    have hneg : profit P p2 t ϕ2 ≤ 0 := by
      unfold profit; rw [hd2]
      have : P.b * ϕ2 ≥ 0 := mul_nonneg hP.2.2.2.2.2.2.1.le h2.1
      nlinarith
    exact hneg.trans (optProfit_nonneg P hP h2.1 h2.2)

lemma omega_sq (P : Params) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) :
    ωθ P ϕ ^ 2 = P.βr ^ 2 * (1 - ϕ ^ 2) + P.ωY ^ 2 := by
  unfold ωθ
  rw [Real.sq_sqrt]
  nlinarith [mul_nonneg (sq_nonneg P.βr) (show 0 ≤ 1 - ϕ ^ 2 by nlinarith), sq_nonneg P.ωY]

lemma omega_one (P : Params) (hY : 0 < P.ωY) : ωθ P 1 = P.ωY := by
  unfold ωθ
  rw [show P.βr ^ 2 * (1 - (1:ℝ) ^ 2) + P.ωY ^ 2 = P.ωY ^ 2 by ring]
  exact Real.sqrt_sq hY.le

lemma omega_lt (P : Params) (hP : Standing P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : ωθ P b < ωθ P a := by
  have e1 := omega_sq P ha (hab.le.trans hb)
  have e2 := omega_sq P (ha.trans hab.le) hb
  have p1 := omega_pos P hP.2.2.2.2.1 ha (hab.le.trans hb)
  have p2 := omega_pos P hP.2.2.2.2.1 (ha.trans hab.le) hb
  have hβ : 0 < P.βr ^ 2 := by have := hP.2.1; positivity
  by_contra hc
  push Not at hc
  have : ωθ P a ^ 2 ≤ ωθ P b ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left (show a ^ 2 < b ^ 2 by nlinarith) hβ]

lemma opt_eq (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1)
    {x : ℝ × ℝ} (hx : IsOptimal P ϕ x) : optProfit P ϕ = profit P x.1 x.2 ϕ := by
  apply le_antisymm
  · refine csSup_le ⟨_, x, hx.1, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hx.2 y hy
  · exact le_csSup (profit_bdd P hP h0 h1) ⟨x, hx.1, rfl⟩

lemma optPlan_spec (P : Params) {ϕ : ℝ} (h : ∃ x, IsOptimal P ϕ x) :
    IsOptimal P ϕ (optPlan P ϕ) := by
  simp only [optPlan, dif_pos h]
  exact h.choose_spec

/-- Step F: under (23), every effort below 1 earns strictly more than full effort. -/
lemma stepF (P : Params) (hP : Standing P) (hopt : IsOptimal P 1 (optPlan P 1))
    (h23 : cond23 P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ < 1) :
    optProfit P 1 < optProfit P ϕ := by
  have hP' : Standing P := hP
  obtain ⟨hΛ, hβr, hβt, hρ, hY, hc, hb, -⟩ := hP
  have htr := transport P hP' (ϕ1 := 1) (ϕ2 := ϕ) ⟨zero_le_one, le_rfl⟩ ⟨h0, h1.le⟩
    (p := (optPlan P 1).1) (t := (optPlan P 1).2) hopt.1
  rw [← opt_eq P hP' zero_le_one le_rfl hopt] at htr
  have hρ' : 0 ≤ P.βr * P.ρ := by positivity
  have hl := (dem_fix P hΛ hρ' (p := (optPlan P 1).1) (t := (optPlan P 1).2)
    (omega_pos P hY zero_le_one le_rfl) hopt.1.2.1).1
  set l := dem P (optPlan P 1).1 (optPlan P 1).2 1 with hldef
  have hD : idx P (optPlan P 1).1 (optPlan P 1).2 1 = (optV P 1 - P.Ve) / P.ωY := by
    unfold idx optV optDem; rw [omega_one P hY]
  rw [hD, omega_one P hY] at htr
  set D := (optV P 1 - P.Ve) / P.ωY with hDdef
  have hω := omega_pos P hY h0 h1.le
  have hsq := omega_sq P h0 h1.le
  have hβ2 : 0 < P.βr ^ 2 := by positivity
  have hgt : P.ωY < ωθ P ϕ := by
    by_contra hcon; push Not at hcon
    have : ωθ P ϕ ^ 2 ≤ P.ωY ^ 2 := by nlinarith
    nlinarith [mul_pos hβ2 (show 0 < 1 - ϕ ^ 2 by nlinarith)]
  -- key: (ωϕ - ωY) D < b (1 - ϕ)
  have hkey : (ωθ P ϕ - P.ωY) * D < P.b * (1 - ϕ) := by
    by_cases hDs : D ≤ 0
    · have : (ωθ P ϕ - P.ωY) * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hDs
      nlinarith
    push Not at hDs
    have hDle : D ≤ P.b * P.ωY / P.βr ^ 2 := by
      have h23' : optV P 1 - P.Ve ≤ P.b * P.ωY ^ 2 / P.βr ^ 2 := h23
      rw [hDdef]
      calc (optV P 1 - P.Ve) / P.ωY ≤ (P.b * P.ωY ^ 2 / P.βr ^ 2) / P.ωY :=
            div_le_div_of_nonneg_right h23' hY.le
        _ = P.b * P.ωY / P.βr ^ 2 := by field_simp
    have hA : (ωθ P ϕ - P.ωY) * P.ωY < P.βr ^ 2 * (1 - ϕ) := by
      have e : (ωθ P ϕ - P.ωY) * (ωθ P ϕ + P.ωY) = P.βr ^ 2 * (1 - ϕ) * (1 + ϕ) := by
        nlinarith
      have h2 : P.ωY * (1 + ϕ) < ωθ P ϕ + P.ωY := by nlinarith
      have h3 : (ωθ P ϕ - P.ωY) * (P.ωY * (1 + ϕ)) < (ωθ P ϕ - P.ωY) * (ωθ P ϕ + P.ωY) :=
        mul_lt_mul_of_pos_left h2 (by linarith)
      nlinarith
    calc (ωθ P ϕ - P.ωY) * D ≤ (ωθ P ϕ - P.ωY) * (P.b * P.ωY / P.βr ^ 2) :=
          mul_le_mul_of_nonneg_left hDle (by linarith)
      _ = ((ωθ P ϕ - P.ωY) * P.ωY) * (P.b / P.βr ^ 2) := by ring
      _ < (P.βr ^ 2 * (1 - ϕ)) * (P.b / P.βr ^ 2) := mul_lt_mul_of_pos_right hA (by positivity)
      _ = P.b * (1 - ϕ) := by field_simp
  have hpos : 0 < l * ((P.ωY - ωθ P ϕ) * D - P.b * (ϕ - 1)) := by
    apply mul_pos hl; nlinarith
  linarith

/-- Step D: strict quasiconvexity of the optimal profit on [0,1]. -/
lemma quasi (P : Params) (hP : Standing P) (hex : ∀ ϕ ∈ Icc (0:ℝ) 1, ∃ x, IsOptimal P ϕ x)
    {x y z : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z) (hz : z ≤ 1) :
    optProfit P y < max (optProfit P x) (optProfit P z) := by
  have hy0 : 0 ≤ y := hx.trans hxy.le
  have hy1 : y ≤ 1 := hyz.le.trans hz
  obtain ⟨⟨p, t⟩, hopt⟩ := hex y ⟨hy0, hy1⟩
  have hG := opt_eq P hP hy0 hy1 hopt
  simp only at hG
  have hvx := transport P hP (ϕ1 := y) (ϕ2 := x) ⟨hy0, hy1⟩ ⟨hx, hxy.le.trans hy1⟩ hopt.1
  have hvz := transport P hP (ϕ1 := y) (ϕ2 := z) ⟨hy0, hy1⟩ ⟨hy0.trans hyz.le, hz⟩ hopt.1
  rw [← hG] at hvx hvz
  have hρ' : 0 ≤ P.βr * P.ρ := by have := hP.2.1; have := hP.2.2.2.1; positivity
  have hl := (dem_fix P hP.1 hρ' (p := p) (t := t)
    (omega_pos P hP.2.2.2.2.1 hy0 hy1) hopt.1.2.1).1
  set l := dem P p t y
  set D := idx P p t y
  set a := ωθ P x with ha
  set bb := ωθ P y with hbb
  set cc := ωθ P z with hcc
  have hab : bb < a := omega_lt P hP hx hxy hy1
  have hbc : cc < bb := omega_lt P hP hy0 hyz hz
  have pc : 0 < cc := omega_pos P hP.2.2.2.2.1 (hy0.trans hyz.le) hz
  have e1 : (a - bb) * (a + bb) = P.βr ^ 2 * (y - x) * (y + x) := by
    have := omega_sq P hx (hxy.le.trans hy1); have := omega_sq P hy0 hy1
    rw [← ha] at *; rw [← hbb] at *; nlinarith
  have e2 : (bb - cc) * (bb + cc) = P.βr ^ 2 * (z - y) * (z + y) := by
    have := omega_sq P hy0 hy1; have := omega_sq P (hy0.trans hyz.le) hz
    rw [← hbb] at *; rw [← hcc] at *; nlinarith
  set K := (bb - cc) * (y - x) - (a - bb) * (z - y) with hK
  have hβ2 : 0 < P.βr ^ 2 := by have := hP.2.1; positivity
  have hK' : K * ((a + bb) * (bb + cc)) =
      (y - x) * (z - y) * P.βr ^ 2 * ((z + y) * (a + bb) - (y + x) * (bb + cc)) := by
    rw [hK]; linear_combination (y - x) * (a + bb) * e2 - (z - y) * (bb + cc) * e1
  have hbr : 0 < (z + y) * (a + bb) - (y + x) * (bb + cc) := by
    have h1 : (y + x) * (a + bb) < (z + y) * (a + bb) :=
      mul_lt_mul_of_pos_right (by linarith) (by linarith)
    have h2 : (y + x) * (bb + cc) ≤ (y + x) * (a + bb) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hKpos : 0 < K := by
    have hr : 0 < K * ((a + bb) * (bb + cc)) := by
      rw [hK']
      have : 0 < (y - x) * (z - y) := mul_pos (by linarith) (by linarith)
      exact mul_pos (mul_pos this hβ2) hbr
    by_contra hk; push Not at hk
    have : K * ((a + bb) * (bb + cc)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hk (mul_pos (by linarith) (by linarith)).le
    linarith
  have hM1 : optProfit P x ≤ max (optProfit P x) (optProfit P z) := le_max_left _ _
  have hM2 : optProfit P z ≤ max (optProfit P x) (optProfit P z) := le_max_right _ _
  set M := max (optProfit P x) (optProfit P z)
  have i1 := mul_le_mul_of_nonneg_left (hvx.trans hM1) (show 0 ≤ bb - cc by linarith)
  have i2 := mul_le_mul_of_nonneg_left (hvz.trans hM2) (show 0 ≤ a - bb by linarith)
  have hlbK : 0 < l * P.b * K := mul_pos (mul_pos hl hP.2.2.2.2.2.2.1) hKpos
  have hfin : (a - cc) * optProfit P y < (a - cc) * M := by
    rw [hK] at hlbK
    nlinarith
  exact lt_of_mul_lt_mul_left hfin (by linarith)

open Filter Topology in
lemma lsc (P : Params) (hP : Standing P) : LowerSemicontinuousOn (optProfit P) (Icc 0 1) := by
  intro x hx y hy
  have hne : ((fun x' : ℝ × ℝ => profit P x'.1 x'.2 x) '' {x' | Feasible P x x'}).Nonempty :=
    ⟨_, _, (nonneg_plan P hP hx.1 hx.2).1, rfl⟩
  obtain ⟨_, ⟨⟨p, t⟩, hf, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hy
  have hc : Continuous (fun ϕ' => profit P p t x +
      dem P p t x * ((ωθ P x - ωθ P ϕ') * idx P p t x - P.b * (ϕ' - x))) := by
    unfold ωθ; fun_prop
  have hlt' : y < profit P p t x +
      dem P p t x * ((ωθ P x - ωθ P x) * idx P p t x - P.b * (x - x)) := by
    simp only [sub_self, zero_mul, mul_zero, add_zero]; exact hlt
  have hev := (hc.tendsto x).eventually (lt_mem_nhds hlt')
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ϕ' h1 h2
  exact h1.trans_le (transport P hP hx h2 hf)

lemma shape (g : ℝ → ℝ)
    (hq : ∀ x y z : ℝ, 0 ≤ x → x < y → y < z → z ≤ 1 → g y < max (g x) (g z))
    {ϕ0 : ℝ} (h0 : ϕ0 ∈ Icc (0:ℝ) 1) (hmin : ∀ ϕ ∈ Icc (0:ℝ) 1, g ϕ0 ≤ g ϕ) :
    StrictAntiOn g (Icc 0 ϕ0) ∧ StrictMonoOn g (Icc ϕ0 1) := by
  constructor
  · intro a ha b hb hab
    rcases lt_or_eq_of_le hb.2 with hb' | hb'
    · have h := hq a b ϕ0 ha.1 hab hb' h0.2
      have hm := hmin b ⟨ha.1.trans hab.le, hb.2.trans h0.2⟩
      rcases max_cases (g a) (g ϕ0) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at h <;> linarith
    · rw [hb'] at hab ⊢
      have h := hq a ((a + ϕ0) / 2) ϕ0 ha.1 (by linarith) (by linarith) h0.2
      have hm := hmin ((a + ϕ0) / 2) ⟨by linarith [ha.1], by linarith [h0.2]⟩
      rcases max_cases (g a) (g ϕ0) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at h <;> linarith
  · intro a ha b hb hab
    rcases lt_or_eq_of_le ha.1 with ha' | ha'
    · have h := hq ϕ0 a b h0.1 ha' hab hb.2
      have hm := hmin a ⟨h0.1.trans ha.1, ha.2⟩
      rcases max_cases (g ϕ0) (g b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at h <;> linarith
    · rw [← ha'] at hab ⊢
      have h := hq ϕ0 ((ϕ0 + b) / 2) b h0.1 (by linarith) (by linarith) hb.2
      have hm := hmin ((ϕ0 + b) / 2) ⟨by linarith [h0.1], by linarith [hb.2]⟩
      rcases max_cases (g ϕ0) (g b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at h <;> linarith

theorem assemble (P : Params) (hP : Standing P)
    (hex : ∀ ϕ ∈ Icc (0:ℝ) 1, ∃ x, IsOptimal P ϕ x)
    (hG : ∃ a ∈ Ioc (0:ℝ) 1, optProfit P a < optProfit P 0)
    (hH : ¬ cond23 P → ∃ c ∈ Ico (0:ℝ) 1, optProfit P c < optProfit P 1) :
    (cond23 P → StrictAntiOn (optProfit P) (Set.Icc 0 1)) ∧
      (¬ cond23 P → ∃ ϕ0 ∈ Set.Ioo (0 : ℝ) 1,
        StrictAntiOn (optProfit P) (Set.Icc 0 ϕ0) ∧ StrictMonoOn (optProfit P) (Set.Icc ϕ0 1)) ∧
      ∀ ϕ ∈ Set.Ioo (0 : ℝ) 1, optProfit P ϕ < max (optProfit P 0) (optProfit P 1) := by
  have hq : ∀ x y z : ℝ, 0 ≤ x → x < y → y < z → z ≤ 1 →
      optProfit P y < max (optProfit P x) (optProfit P z) :=
    fun x y z h1 h2 h3 h4 => quasi P hP hex h1 h2 h3 h4
  have hopt1 := optPlan_spec P (hex 1 ⟨zero_le_one, le_rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro h23
    have hmin : ∀ ϕ ∈ Icc (0:ℝ) 1, optProfit P 1 ≤ optProfit P ϕ := by
      intro ϕ hϕ
      rcases lt_or_eq_of_le hϕ.2 with h | h
      · exact (stepF P hP hopt1 h23 hϕ.1 h).le
      · rw [h]
    exact (shape _ hq ⟨zero_le_one, le_rfl⟩ hmin).1
  · intro h23
    obtain ⟨ϕ0, hϕ0, hmin⟩ :=
      (lsc P hP).exists_isMinOn ⟨0, left_mem_Icc.2 zero_le_one⟩ isCompact_Icc
    have hmin' : ∀ ϕ ∈ Icc (0:ℝ) 1, optProfit P ϕ0 ≤ optProfit P ϕ :=
      fun ϕ hϕ => isMinOn_iff.1 hmin ϕ hϕ
    obtain ⟨a, ha, hga⟩ := hG
    obtain ⟨c, hc, hgc⟩ := hH h23
    refine ⟨ϕ0, ⟨?_, ?_⟩, shape _ hq hϕ0 hmin'⟩
    · rcases lt_or_eq_of_le hϕ0.1 with h | h
      · exact h
      · exfalso; rw [← h] at hmin'; have := hmin' a ⟨ha.1.le, ha.2⟩; linarith
    · rcases lt_or_eq_of_le hϕ0.2 with h | h
      · exact h
      · exfalso; rw [h] at hmin'; have := hmin' c ⟨hc.1, hc.2.le⟩; linarith
  · intro ϕ hϕ
    exact hq 0 ϕ 1 le_rfl hϕ.1 hϕ.2 le_rfl

/-! ### Existence of an optimal plan (reparametrize by the index D and the time t) -/

/-- the price that yields index `D` (demand `Λσ(D)`) at time `t` -/
noncomputable def price (P : Params) (ϕ D t : ℝ) : ℝ :=
  P.α + P.βr * P.ρ * (1 - Real.exp (-(P.μ - P.Λ * sigmoid D) * t)) - P.βt * t - P.Ve -
    ωθ P ϕ * D

lemma rho_nonneg (P : Params) (hP : Standing P) : 0 ≤ P.βr * P.ρ := by
  have := hP.2.1; have := hP.2.2.2.1; positivity

lemma dem_price (P : Params) (hP : Standing P) {ϕ t : ℝ} (hω : 0 < ωθ P ϕ) (ht : 0 ≤ t)
    (D : ℝ) : dem P (price P ϕ D t) t ϕ = P.Λ * sigmoid D := by
  have hΛ := hP.1
  apply dem_eq_of_fix P hΛ (rho_nonneg P hP) hω ht (mul_pos hΛ (sigmoid_pos D)).le
    (by nlinarith [sigmoid_lt_one D])
  have : Vdet P (price P ϕ D t) t (P.Λ * sigmoid D) - P.Ve = ωθ P ϕ * D := by
    unfold Vdet price; ring
  rw [this, mul_div_cancel_left₀ _ hω.ne']

lemma idx_price (P : Params) (hP : Standing P) {ϕ t : ℝ} (hω : 0 < ωθ P ϕ) (ht : 0 ≤ t)
    (D : ℝ) : idx P (price P ϕ D t) t ϕ = D := by
  unfold idx
  rw [dem_price P hP hω ht D]
  have : Vdet P (price P ϕ D t) t (P.Λ * sigmoid D) - P.Ve = ωθ P ϕ * D := by
    unfold Vdet price; ring
  rw [this, mul_div_cancel_left₀ _ hω.ne']

lemma plan_repr (P : Params) (hP : Standing P) {ϕ p t : ℝ} (hω : 0 < ωθ P ϕ) (ht : 0 ≤ t) :
    dem P p t ϕ = P.Λ * sigmoid (idx P p t ϕ) ∧ p = price P ϕ (idx P p t ϕ) t := by
  obtain ⟨-, -, hfix⟩ := dem_fix P hP.1 (rho_nonneg P hP) (p := p) hω ht
  have h1 : dem P p t ϕ = P.Λ * sigmoid (idx P p t ϕ) := by rw [idx]; exact hfix
  refine ⟨h1, ?_⟩
  have h2 : ωθ P ϕ * idx P p t ϕ = Vdet P p t (dem P p t ϕ) - P.Ve := by
    unfold idx; field_simp
  unfold price; rw [← h1, h2]; unfold Vdet; ring

lemma profit_le_t (P : Params) (hP : Standing P) {ϕ p t : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1)
    (hp : P.c ≤ p) (ht : 0 ≤ t) :
    profit P p t ϕ ≤
      P.Λ * exp ((P.α + P.βr * P.ρ - P.βt * t - P.Ve) / ωθ P ϕ) * ωθ P ϕ := by
  obtain ⟨hΛ, hβr, hβt, hρ, hY, hc, hb, -⟩ := hP
  have hω := omega_pos P hY h0 h1
  have hρ' : 0 ≤ P.βr * P.ρ := by positivity
  set ω := ωθ P ϕ with hωdef
  set A := P.α + P.βr * P.ρ - P.βt * t - P.Ve with hA
  obtain ⟨hl0, -, hfix⟩ := dem_fix P hΛ hρ' (p := p) hω ht
  set l := dem P p t ϕ with hl
  unfold profit
  rw [← hl]
  by_cases hm : p - P.b * ϕ - P.c ≤ 0
  · have : 0 < P.Λ * exp (A / ω) * ω := by positivity
    nlinarith
  push Not at hm
  have hV : Vdet P p t l - P.Ve ≤ A - p := by
    unfold Vdet; rw [hA]
    have := exp_pos (-(P.μ - l) * t)
    nlinarith [mul_nonneg hρ' this.le]
  have hσ : sigmoid ((Vdet P p t l - P.Ve) / ω) ≤ exp (A / ω) * exp (-(p / ω)) := by
    rw [← exp_add]
    refine (sigmoid_le_exp _).trans (exp_le_exp.2 ?_)
    have : A / ω + -(p / ω) = (A - p) / ω := by ring
    rw [this]; exact div_le_div_of_nonneg_right hV hω.le
  have hxe : (p / ω) * exp (-(p / ω)) ≤ 1 := by
    have h1 := Real.add_one_le_exp (p / ω)
    have h2 : exp (p / ω) * exp (-(p / ω)) = 1 := by rw [← exp_add]; simp
    have h3 := exp_pos (-(p / ω))
    nlinarith
  have hpe : p * exp (-(p / ω)) ≤ ω := by
    have : p * exp (-(p / ω)) = ω * ((p / ω) * exp (-(p / ω))) := by field_simp
    rw [this]; nlinarith
  have hmarg : p - P.b * ϕ - P.c ≤ p := by nlinarith
  have hlb : l ≤ P.Λ * (exp (A / ω) * exp (-(p / ω))) := by
    rw [hfix]; exact mul_le_mul_of_nonneg_left hσ hΛ.le
  calc l * (p - P.b * ϕ - P.c) ≤ l * p := mul_le_mul_of_nonneg_left hmarg hl0.le
    _ ≤ P.Λ * (exp (A / ω) * exp (-(p / ω))) * p :=
        mul_le_mul_of_nonneg_right hlb (by linarith)
    _ = P.Λ * exp (A / ω) * (p * exp (-(p / ω))) := by ring
    _ ≤ P.Λ * exp (A / ω) * ω := mul_le_mul_of_nonneg_left hpe (by positivity)

lemma profit_le_D (P : Params) (hP : Standing P) {ϕ p t : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1)
    (ht : 0 ≤ t) (hD : idx P p t ϕ ≤ 0) :
    profit P p t ϕ ≤ P.Λ * exp (idx P p t ϕ / 2) *
      (|P.α + P.βr * P.ρ - P.Ve - P.c| + 2 * ωθ P ϕ) := by
  have hω := omega_pos P hP.2.2.2.2.1 h0 h1
  obtain ⟨hdem, hp⟩ := plan_repr P hP (p := p) hω ht
  set D := idx P p t ϕ with hDdef
  set ω := ωθ P ϕ
  set A1 := P.α + P.βr * P.ρ - P.Ve - P.c
  have hΛ := hP.1
  have hb := hP.2.2.2.2.2.2.1
  have hρ' := rho_nonneg P hP
  unfold profit
  rw [hdem]
  have hE : 0 < exp (D / 2) := exp_pos _
  by_cases hm : p - P.b * ϕ - P.c ≤ 0
  · have : 0 ≤ P.Λ * exp (D / 2) * (|A1| + 2 * ω) := by positivity
    have : 0 ≤ P.Λ * sigmoid D := (mul_pos hΛ (sigmoid_pos D)).le
    nlinarith
  push Not at hm
  have hmarg : p - P.b * ϕ - P.c ≤ |A1| + ω * (-D) := by
    rw [hp]; unfold price
    have he := exp_pos (-(P.μ - P.Λ * sigmoid D) * t)
    have ha := le_abs_self A1
    nlinarith [mul_nonneg hρ' he.le, mul_nonneg hP.2.2.1.le ht, mul_nonneg hb.le h0]
  have hσ : sigmoid D ≤ exp (D / 2) * exp (D / 2) := by
    rw [← exp_add]; simpa using sigmoid_le_exp D
  have hx : (-D) * exp (D / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-D / 2)
    have h2 : exp (-D / 2) * exp (D / 2) = 1 := by
      rw [← exp_add, show -D / 2 + D / 2 = 0 by ring, exp_zero]
    nlinarith
  have hE1 : exp (D / 2) ≤ 1 := by rw [exp_le_one_iff]; linarith
  calc P.Λ * sigmoid D * (p - P.b * ϕ - P.c)
      ≤ P.Λ * (exp (D / 2) * exp (D / 2)) * (|A1| + ω * (-D)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hσ hΛ.le) hmarg hm.le (by positivity)
    _ = P.Λ * exp (D / 2) * (exp (D / 2) * |A1| + ω * ((-D) * exp (D / 2))) := by ring
    _ ≤ P.Λ * exp (D / 2) * (|A1| + 2 * ω) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := abs_nonneg A1
        nlinarith

lemma exists_opt (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) (Dc : ℝ)
    (hgood : ∃ p t, Feasible P ϕ (p, t) ∧ idx P p t ϕ ≤ Dc ∧ 0 < profit P p t ϕ) :
    ∃ p t, Feasible P ϕ (p, t) ∧ idx P p t ϕ ≤ Dc ∧
      ∀ p' t', Feasible P ϕ (p', t') → idx P p' t' ϕ ≤ Dc →
        profit P p' t' ϕ ≤ profit P p t ϕ := by
  obtain ⟨pg, tg, hfg, hDg, hπg⟩ := hgood
  have hω := omega_pos P hP.2.2.2.2.1 h0 h1
  have hΛ := hP.1
  have hβt := hP.2.2.1
  obtain ⟨B, hB⟩ : ∃ B, B = |P.α + P.βr * P.ρ - P.Ve - P.c| + 2 * ωθ P ϕ := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; have := abs_nonneg (P.α + P.βr * P.ρ - P.Ve - P.c); linarith
  obtain ⟨πg, hπgd⟩ : ∃ πg, πg = profit P pg tg ϕ := ⟨_, rfl⟩
  rw [← hπgd] at hπg
  obtain ⟨r, hr⟩ : ∃ r, r = πg / (P.Λ * B + 1) := ⟨_, rfl⟩
  obtain ⟨r', hr'⟩ : ∃ r', r' = πg / (P.Λ * ωθ P ϕ + 1) := ⟨_, rfl⟩
  have hd1 : 0 < P.Λ * B + 1 := by nlinarith
  have hd2 : 0 < P.Λ * ωθ P ϕ + 1 := by nlinarith
  have hrpos : 0 < r := by rw [hr]; exact div_pos hπg hd1
  have hr'pos : 0 < r' := by rw [hr']; exact div_pos hπg hd2
  have hrr : r * (P.Λ * B + 1) = πg := by rw [hr]; field_simp
  have hrr' : r' * (P.Λ * ωθ P ϕ + 1) = πg := by rw [hr']; field_simp
  obtain ⟨M, hM⟩ : ∃ M, M = max (-idx P pg tg ϕ) (2 * |Real.log r|) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = max tg ((|P.α + P.βr * P.ρ - P.Ve| +
      ωθ P ϕ * |Real.log r'|) / P.βt) := ⟨_, rfl⟩
  have hM1 : -idx P pg tg ϕ ≤ M := by rw [hM]; exact le_max_left _ _
  have hM2 : 2 * |Real.log r| ≤ M := by rw [hM]; exact le_max_right _ _
  have hT1 : tg ≤ T := by rw [hT]; exact le_max_left _ _
  have hT2 : (|P.α + P.βr * P.ρ - P.Ve| + ωθ P ϕ * |Real.log r'|) / P.βt ≤ T := by
    rw [hT]; exact le_max_right _ _
  let v : ℝ × ℝ → ℝ := fun z => P.Λ * sigmoid z.1 * (price P ϕ z.1 z.2 - P.b * ϕ - P.c)
  let K : Set (ℝ × ℝ) := {z | -M ≤ z.1 ∧ z.1 ≤ Dc ∧ 0 ≤ z.2 ∧ z.2 ≤ T ∧
    1 ≤ (P.μ - P.Λ * sigmoid z.1) * z.2 ∧ P.c ≤ price P ϕ z.1 z.2}
  have hpc : Continuous (fun z : ℝ × ℝ => price P ϕ z.1 z.2) := by unfold price; fun_prop
  have hvc : Continuous v := by
    show Continuous (fun z : ℝ × ℝ => P.Λ * sigmoid z.1 * (price P ϕ z.1 z.2 - P.b * ϕ - P.c))
    fun_prop
  have hKc : IsCompact K := by
    apply (isCompact_Icc (a := ((-M, 0) : ℝ × ℝ)) (b := (Dc, T))).of_isClosed_subset
    · show IsClosed {z : ℝ × ℝ | -M ≤ z.1 ∧ z.1 ≤ Dc ∧ 0 ≤ z.2 ∧ z.2 ≤ T ∧
        1 ≤ (P.μ - P.Λ * sigmoid z.1) * z.2 ∧ P.c ≤ price P ϕ z.1 z.2}
      simp only [Set.setOf_and]
      refine (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le continuous_const hpc)))))
    · rintro z ⟨h1, h2, h3, h4, -, -⟩
      exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  obtain ⟨hpg, htg, hcapg⟩ := hfg
  simp only at hpg htg hcapg
  obtain ⟨hdemg, hpg'⟩ := plan_repr P hP (p := pg) (t := tg) hω htg
  have hgK : (idx P pg tg ϕ, tg) ∈ K := by
    refine ⟨by linarith, hDg, htg, hT1, ?_, ?_⟩
    · show 1 ≤ (P.μ - P.Λ * sigmoid (idx P pg tg ϕ)) * tg
      rw [← hdemg]; exact hcapg
    · show P.c ≤ price P ϕ (idx P pg tg ϕ) tg
      rw [← hpg']; exact hpg
  have hvg : v (idx P pg tg ϕ, tg) = πg := by
    show P.Λ * sigmoid (idx P pg tg ϕ) * (price P ϕ (idx P pg tg ϕ) tg - P.b * ϕ - P.c) = πg
    rw [← hpg', ← hdemg, hπgd]; rfl
  obtain ⟨z, hzK, hzmax⟩ := hKc.exists_isMaxOn ⟨_, hgK⟩ hvc.continuousOn
  have hzv : πg ≤ v z := hvg ▸ isMaxOn_iff.1 hzmax _ hgK
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩ := hzK
  refine ⟨price P ϕ z.1 z.2, z.2, ⟨hz6, hz3, ?_⟩, ?_, ?_⟩
  · show 1 ≤ (P.μ - dem P (price P ϕ z.1 z.2) z.2 ϕ) * z.2
    rw [dem_price P hP hω hz3]; exact hz5
  · rw [idx_price P hP hω hz3]; exact hz2
  · intro p' t' hf' hD'
    obtain ⟨hp', ht', hcap'⟩ := hf'
    simp only at hp' ht' hcap'
    obtain ⟨hdem', hpr'⟩ := plan_repr P hP (p := p') (t := t') hω ht'
    have hval : profit P (price P ϕ z.1 z.2) z.2 ϕ = v z := by
      show _ = P.Λ * sigmoid z.1 * (price P ϕ z.1 z.2 - P.b * ϕ - P.c)
      unfold profit; rw [dem_price P hP hω hz3]
    have hval' : profit P p' t' ϕ = v (idx P p' t' ϕ, t') := by
      show _ = P.Λ * sigmoid (idx P p' t' ϕ) * (price P ϕ (idx P p' t' ϕ) t' - P.b * ϕ - P.c)
      rw [← hpr', ← hdem']; rfl
    rw [hval]
    by_cases hin : (idx P p' t' ϕ, t') ∈ K
    · rw [hval']; exact isMaxOn_iff.1 hzmax _ hin
    · have hlt : profit P p' t' ϕ < πg := by
        have hin' : ¬ (-M ≤ idx P p' t' ϕ ∧ idx P p' t' ϕ ≤ Dc ∧ 0 ≤ t' ∧ t' ≤ T ∧
            1 ≤ (P.μ - P.Λ * sigmoid (idx P p' t' ϕ)) * t' ∧
            P.c ≤ price P ϕ (idx P p' t' ϕ) t') := hin
        simp only [not_and_or, not_le] at hin'
        rcases hin' with h | h | h | h | h | h
        · -- small index
          have hab := abs_nonneg (Real.log r)
          have hDn : idx P p' t' ϕ ≤ 0 := by linarith
          have hb := profit_le_D P hP h0 h1 ht' hDn
          rw [← hB] at hb
          have e1 : idx P p' t' ϕ / 2 ≤ -|Real.log r| := by linarith
          have e2 : exp (idx P p' t' ϕ / 2) ≤ r := by
            calc exp (idx P p' t' ϕ / 2) ≤ exp (-|Real.log r|) := exp_le_exp.2 e1
              _ ≤ exp (Real.log r) := exp_le_exp.2 (neg_abs_le _)
              _ = r := exp_log hrpos
          have e3 : P.Λ * exp (idx P p' t' ϕ / 2) * B ≤ P.Λ * r * B :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hΛ.le) hBpos.le
          linarith
        · exact absurd hD' (not_le.2 h)
        · linarith
        · -- long delivery time
          have hb := profit_le_t P hP h0 h1 hp' ht'
          have hTb : |P.α + P.βr * P.ρ - P.Ve| + ωθ P ϕ * |Real.log r'| ≤ P.βt * T := by
            rw [div_le_iff₀ hβt] at hT2; linarith
          have hle := le_abs_self (P.α + P.βr * P.ρ - P.Ve)
          have hla := neg_abs_le (Real.log r')
          have e1 : (P.α + P.βr * P.ρ - P.βt * t' - P.Ve) / ωθ P ϕ ≤ Real.log r' := by
            rw [div_le_iff₀ hω]
            have : P.βt * T < P.βt * t' := mul_lt_mul_of_pos_left h hβt
            have := mul_le_mul_of_nonneg_left hla hω.le
            linarith
          have e2 : exp ((P.α + P.βr * P.ρ - P.βt * t' - P.Ve) / ωθ P ϕ) ≤ r' :=
            (exp_le_exp.2 e1).trans (exp_log hr'pos).le
          have e3 : P.Λ * exp ((P.α + P.βr * P.ρ - P.βt * t' - P.Ve) / ωθ P ϕ) * ωθ P ϕ ≤
              P.Λ * r' * ωθ P ϕ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hΛ.le) hω.le
          linarith
        · rw [hdem'] at hcap'; linarith
        · rw [← hpr'] at h; linarith
      linarith

lemma idx_le (P : Params) (hP : Standing P) {ϕ p t : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1)
    (hp : P.c ≤ p) (ht : 0 ≤ t) : idx P p t ϕ ≤ |Vbar P - P.Ve| / ωθ P ϕ := by
  have hω := omega_pos P hP.2.2.2.2.1 h0 h1
  unfold idx
  apply div_le_div_of_nonneg_right _ hω.le
  have := Vdet_le_Vbar P (rho_nonneg P hP) hP.2.2.1 (l := dem P p t ϕ) hp ht
  have := le_abs_self (Vbar P - P.Ve)
  linarith

lemma pos_plan (P : Params) (hP : Standing P) {ϕ : ℝ} (h0 : 0 ≤ ϕ) (h1 : ϕ ≤ 1) :
    Feasible P ϕ (P.c + P.b + 1, 1 / kap P) ∧ 0 < profit P (P.c + P.b + 1) (1 / kap P) ϕ := by
  have hk := kap_pos P hP
  have hb := hP.2.2.2.2.2.2.1
  have ht : (0 : ℝ) ≤ 1 / kap P := by positivity
  have hm := cap_margin P hP h0 h1 (p := P.c + P.b + 1) (by linarith) ht
  have hω := omega_pos P hP.2.2.2.2.1 h0 h1
  have hd := (dem_fix P hP.1 (rho_nonneg P hP) (p := P.c + P.b + 1) hω ht).1
  refine ⟨⟨by simp; linarith, ht, ?_⟩, ?_⟩
  · simp only
    rw [mul_one_div, le_div_iff₀ hk]; linarith
  · unfold profit
    apply mul_pos hd; nlinarith

theorem hex (P : Params) (hP : Standing P) : ∀ ϕ ∈ Icc (0:ℝ) 1, ∃ x, IsOptimal P ϕ x := by
  intro ϕ hϕ
  obtain ⟨hf, hpos⟩ := pos_plan P hP hϕ.1 hϕ.2
  obtain ⟨p, t, hf', -, hmax⟩ := exists_opt P hP hϕ.1 hϕ.2 (|Vbar P - P.Ve| / ωθ P ϕ)
    ⟨_, _, hf, idx_le P hP hϕ.1 hϕ.2 hf.1 hf.2.1, hpos⟩
  refine ⟨(p, t), hf', ?_⟩
  rintro ⟨p', t'⟩ hy
  exact hmax p' t' hy (idx_le P hP hϕ.1 hϕ.2 hy.1 hy.2.1)

/-- Step G: some positive effort earns strictly less than zero effort. -/
theorem stepG (P : Params) (hP : Standing P) :
    ∃ a ∈ Ioc (0:ℝ) 1, optProfit P a < optProfit P 0 := by
  have hb := hP.2.2.2.2.2.2.1
  have hY := hP.2.2.2.2.1
  have hβ : 0 < P.βr ^ 2 := by have := hP.2.1; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = |Vbar P - P.Ve| := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact abs_nonneg _
  have hN : 0 < P.b * P.ωY ^ 2 := by positivity
  have hden : 0 < P.b * P.ωY ^ 2 + P.βr ^ 2 * (E + 1) := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = P.b * P.ωY ^ 2 / (P.b * P.ωY ^ 2 + P.βr ^ 2 * (E + 1)) :=
    ⟨_, rfl⟩
  have haeq : a * (P.b * P.ωY ^ 2 + P.βr ^ 2 * (E + 1)) = P.b * P.ωY ^ 2 := by
    rw [ha]; field_simp
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hden]; nlinarith [mul_pos hβ (show (0:ℝ) < E + 1 by linarith)]
  refine ⟨a, ⟨ha0, ha1.le⟩, ?_⟩
  obtain ⟨⟨p, t⟩, hopt⟩ := hex P hP a ⟨ha0.le, ha1.le⟩
  have hG := opt_eq P hP ha0.le ha1.le hopt
  simp only at hG
  have htr := transport P hP (ϕ1 := a) (ϕ2 := 0) ⟨ha0.le, ha1.le⟩ ⟨le_rfl, zero_le_one⟩ hopt.1
  rw [← hG] at htr
  have hl := (dem_fix P hP.1 (rho_nonneg P hP) (p := p) (t := t)
    (omega_pos P hY ha0.le ha1.le) hopt.1.2.1).1
  have hDle := idx_le P hP ha0.le ha1.le hopt.1.1 hopt.1.2.1
  rw [← hE] at hDle
  have hωa := omega_pos P hY ha0.le ha1.le
  have hω0 := omega_pos P hY le_rfl zero_le_one
  have sa := omega_sq P ha0.le ha1.le
  have s0 := omega_sq P le_rfl zero_le_one
  have hu : 0 ≤ ωθ P 0 - ωθ P a := sub_nonneg.2 (omega_lt P hP le_rfl ha0 ha1.le).le
  generalize idx P p t a = D at htr hDle
  generalize dem P p t a = l at htr hl
  generalize ωθ P a = wa at htr hDle hωa sa hu
  generalize ωθ P 0 = w0 at htr hω0 s0 hu
  have hDw : D * wa ≤ E := by rwa [le_div_iff₀ hωa] at hDle
  have hue : (w0 - wa) * (w0 + wa) = P.βr ^ 2 * a ^ 2 := by
    have : (w0 - wa) * (w0 + wa) = w0 ^ 2 - wa ^ 2 := by ring
    rw [this, sa, s0]; ring
  have hwaY : P.ωY ≤ wa := by nlinarith [mul_nonneg hβ.le (show 0 ≤ 1 - a ^ 2 by nlinarith)]
  have hkey : (w0 - wa) * D < P.b * a := by
    by_cases hDs : D ≤ 0
    · have : (w0 - wa) * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu hDs
      have : 0 < P.b * a := mul_pos hb ha0
      linarith
    push Not at hDs
    have i0 : D * P.ωY ≤ D * wa := mul_le_mul_of_nonneg_left hwaY hDs.le
    have i1 : (w0 - wa) * (D * P.ωY) ≤ (w0 - wa) * E :=
      mul_le_mul_of_nonneg_left (i0.trans hDw) hu
    have i2 : (w0 - wa) * P.ωY ≤ P.βr ^ 2 * a ^ 2 := by
      rw [← hue]; exact mul_le_mul_of_nonneg_left (by linarith) hu
    have i3a := mul_le_mul_of_nonneg_right i1 hY.le
    have i3b := mul_le_mul_of_nonneg_left i2 hE0
    have i4 : P.βr ^ 2 * a * E < P.b * P.ωY ^ 2 := by
      have := mul_pos ha0 hN
      have := mul_pos hβ ha0
      nlinarith
    have i5 := mul_lt_mul_of_pos_left i4 ha0
    have : (w0 - wa) * D * P.ωY ^ 2 < P.b * a * P.ωY ^ 2 := by linarith
    have hY2 : 0 < P.ωY ^ 2 := by positivity
    exact lt_of_mul_lt_mul_right this hY2.le
  have hpos : 0 < l * ((wa - w0) * D - P.b * (0 - a)) := by
    apply mul_pos hl; linarith
  linarith

/-- The theorem, given only Step H. -/
theorem main_of_H (P : Params) (hP : Standing P)
    (hH : ¬ cond23 P → ∃ c ∈ Ico (0:ℝ) 1, optProfit P c < optProfit P 1) :
    (cond23 P → StrictAntiOn (optProfit P) (Set.Icc 0 1)) ∧
      (¬ cond23 P → ∃ ϕ0 ∈ Set.Ioo (0 : ℝ) 1,
        StrictAntiOn (optProfit P) (Set.Icc 0 ϕ0) ∧ StrictMonoOn (optProfit P) (Set.Icc ϕ0 1)) ∧
      ∀ ϕ ∈ Set.Ioo (0 : ℝ) 1, optProfit P ϕ < max (optProfit P 0) (optProfit P 1) :=
  assemble P hP (hex P hP) (stepG P hP) hH

noncomputable def cPhi (K0 B c1 μ Λ ω : ℝ) (x : ℝ) : ℝ :=
  x * K0 - B * (x * ((1 + Real.log (c1 * (μ - x))) / (μ - x))) -
    ω * (x * (Real.log x - Real.log (Λ - x)))

noncomputable def cf1 (K0 B c1 μ Λ ω : ℝ) (x : ℝ) : ℝ :=
  K0 - B * ((1 + Real.log (c1 * (μ - x))) / (μ - x)
      + x * Real.log (c1 * (μ - x)) / (μ - x) ^ 2)
      - ω * (Real.log x - Real.log (Λ - x) + 1 + x / (Λ - x))

noncomputable def cf2 (B c1 μ Λ ω : ℝ) (x : ℝ) : ℝ :=
  -B * (2 * Real.log (c1 * (μ - x)) / (μ - x) ^ 2
      + x * (2 * Real.log (c1 * (μ - x)) - 1) / (μ - x) ^ 3)
      - ω * (1 / x + 1 / (Λ - x) + Λ / (Λ - x) ^ 2)

lemma conc_gen (K0 B c1 μ Λ ω a b : ℝ) (hB : 0 < B) (hc1 : 0 < c1) (hω : 0 < ω) (ha : 0 < a)
    (hab : a < b) (hbΛ : b < Λ) (hbμ : b < μ) (hlog : 1 ≤ Real.log (c1 * (μ - b))) :
    StrictConcaveOn ℝ (Icc a b) (cPhi K0 B c1 μ Λ ω) := by
  have hL : ∀ x, x ≤ b → 1 ≤ Real.log (c1 * (μ - x)) := by
    intro x hx
    exact hlog.trans (Real.log_le_log (by nlinarith) (by nlinarith))
  have hq : ∀ x, x < μ → HasDerivAt (fun y => Real.log (c1 * (μ - y))) (-1 / (μ - x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y => c1 * (μ - y)) (c1 * (0 - 1)) x :=
      ((hasDerivAt_const x μ).sub (hasDerivAt_id' x)).const_mul c1
    have h2 := h1.log (mul_pos hc1 (by linarith)).ne'
    convert h2 using 1
    have : μ - x ≠ 0 := by linarith
    field_simp
    ring
  have hd1 : ∀ x ∈ Ioo a b, HasDerivAt (cPhi K0 B c1 μ Λ ω) (cf1 K0 B c1 μ Λ ω x) x := by
    intro x ⟨hxa, hxb⟩
    have hx0 : 0 < x := ha.trans hxa
    have hxμ : x < μ := hxb.trans hbμ
    have hxΛ : x < Λ := hxb.trans hbΛ
    have hd : HasDerivAt (fun y => μ - y) (0 - 1) x := (hasDerivAt_const x μ).sub (hasDerivAt_id' x)
    have hdl : HasDerivAt (fun y => Λ - y) (0 - 1) x := (hasDerivAt_const x Λ).sub (hasDerivAt_id' x)
    have hA : HasDerivAt (fun y => (1 + Real.log (c1 * (μ - y))) / (μ - y))
        (((0 + -1 / (μ - x)) * (μ - x) - (1 + Real.log (c1 * (μ - x))) * (0 - 1)) / (μ - x) ^ 2) x :=
      ((hasDerivAt_const x (1:ℝ)).add (hq x hxμ)).div hd (by linarith)
    have hB2 := ((hasDerivAt_id' x).mul hA).const_mul B
    have hlg : HasDerivAt (fun y => Real.log y - Real.log (Λ - y)) (1 / x - (0 - 1) / (Λ - x)) x := by
      have e1 := (hasDerivAt_id' x).log hx0.ne'
      have e2 := hdl.log (by linarith : Λ - x ≠ 0)
      exact e1.sub e2
    have hC := ((hasDerivAt_id' x).mul hlg).const_mul ω
    have hK := (hasDerivAt_id' x).mul_const K0
    have htot := (hK.sub hB2).sub hC
    refine (htot.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    swap
    · first | rfl | simp [cPhi]
    simp only [cf1]
    have h1 : μ - x ≠ 0 := by linarith
    have h2 : Λ - x ≠ 0 := by linarith
    field_simp
    ring
  have hd2 : ∀ x ∈ Ioo a b, HasDerivAt (cf1 K0 B c1 μ Λ ω) (cf2 B c1 μ Λ ω x) x := by
    intro x ⟨hxa, hxb⟩
    have hx0 : 0 < x := ha.trans hxa
    have hxμ : x < μ := hxb.trans hbμ
    have hxΛ : x < Λ := hxb.trans hbΛ
    have hd : HasDerivAt (fun y => μ - y) (0 - 1) x := (hasDerivAt_const x μ).sub (hasDerivAt_id' x)
    have hdl : HasDerivAt (fun y => Λ - y) (0 - 1) x := (hasDerivAt_const x Λ).sub (hasDerivAt_id' x)
    have hA := ((hasDerivAt_const x (1:ℝ)).add (hq x hxμ)).div hd (by linarith)
    have hA2 := ((hasDerivAt_id' x).mul (hq x hxμ)).div (hd.pow 2) (pow_ne_zero 2 (by linarith : μ - x ≠ 0))
    have hB2 := (hA.add hA2).const_mul B
    have e1 := (hasDerivAt_id' x).log hx0.ne'
    have e2 := hdl.log (by linarith : Λ - x ≠ 0)
    have e3 := (hasDerivAt_id' x).div hdl (by linarith : Λ - x ≠ 0)
    have hC := (((e1.sub e2).add (hasDerivAt_const x (1:ℝ))).add e3).const_mul ω
    have htot := ((hasDerivAt_const x K0).sub hB2).sub hC
    refine (htot.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    swap
    · first | rfl | simp [cf1]
    simp only [cf2, Pi.pow_apply]
    norm_num
    have h1 : μ - x ≠ 0 := by linarith
    have h2 : Λ - x ≠ 0 := by linarith
    field_simp
    ring
  have hneg : ∀ x ∈ Ioo a b, cf2 B c1 μ Λ ω x < 0 := by
    intro x ⟨hxa, hxb⟩
    have hx0 : 0 < x := ha.trans hxa
    have hd0 : 0 < μ - x := by linarith
    have hl0 : 0 < Λ - x := by linarith
    have hLx := hL x hxb.le
    simp only [cf2]
    have t1 : 0 < 2 * Real.log (c1 * (μ - x)) / (μ - x) ^ 2 := by positivity
    have t2 : 0 ≤ x * (2 * Real.log (c1 * (μ - x)) - 1) / (μ - x) ^ 3 := by
      apply div_nonneg (mul_nonneg hx0.le (by linarith)) (by positivity)
    have t3 : 0 < 1 / x + 1 / (Λ - x) + Λ / (Λ - x) ^ 2 := by
      have : 0 < Λ := by linarith
      positivity
    nlinarith [mul_pos hB t1, mul_nonneg hB.le t2, mul_pos hω t3]
  have hanti : StrictAntiOn (cf1 K0 B c1 μ Λ ω) (Ioo a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo a b)
    · intro x hx; exact (hd2 x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hd2 x hx).deriv]; exact hneg x hx
  have hcont : ContinuousOn (cPhi K0 B c1 μ Λ ω) (Icc a b) := by
    intro x ⟨hxa, hxb⟩
    have hx0 : 0 < x := ha.trans_le hxa
    have : ContinuousAt (cPhi K0 B c1 μ Λ ω) x := by
      unfold cPhi
      have h1 : μ - x ≠ 0 := by linarith
      have h2 : c1 * (μ - x) ≠ 0 := (mul_pos hc1 (by linarith)).ne'
      have h3 : Λ - x ≠ 0 := by linarith
      have h4 : x ≠ 0 := hx0.ne'
      fun_prop (disch := assumption)
    exact this.continuousWithinAt
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc a b) hcont
  rw [interior_Icc]
  intro x hx y hy hxy
  rw [(hd1 x hx).deriv, (hd1 y hy).deriv]
  exact hanti hx hy hxy


/-! ### Step H: uniqueness of the optimal demand at full effort, and ϕ0 < 1 -/

noncomputable def Phi (P : Params) : ℝ → ℝ :=
  cPhi (P.α - P.Ve - P.b - P.c + P.βr * P.ρ) P.βt (P.βr * P.ρ / P.βt) P.μ P.Λ P.ωY

lemma one_sub_sig (Λ D : ℝ) : Λ - Λ * sigmoid D = Λ * sigmoid D * exp (-D) := by
  rw [mul_assoc, Real.sigmoid_mul_rexp_neg, Real.sigmoid_neg]; ring

lemma log_sig (Λ D : ℝ) (hΛ : 0 < Λ) :
    Real.log (Λ * sigmoid D) - Real.log (Λ - Λ * sigmoid D) = D := by
  rw [one_sub_sig, Real.log_mul (mul_pos hΛ (sigmoid_pos D)).ne' (exp_pos _).ne', Real.log_exp]
  ring

lemma sig_log {Λ l : ℝ} (hl0 : 0 < l) (hlΛ : l < Λ) :
    Λ * sigmoid (Real.log l - Real.log (Λ - l)) = l := by
  have hd : 0 < Λ - l := by linarith
  rw [Real.sigmoid_def, neg_sub, Real.exp_sub, Real.exp_log hd, Real.exp_log hl0]
  have hl0' : l ≠ 0 := hl0.ne'
  have h2 : 1 + (Λ - l) / l = Λ / l := by field_simp; ring
  rw [h2, inv_div]
  have hΛ0 : Λ ≠ 0 := by linarith
  field_simp

lemma log_ge_one (P : Params) (hP : Standing P) {d : ℝ} (hd : kap P ≤ d) :
    1 ≤ Real.log (P.βr * P.ρ / P.βt * d) := by
  have hβt := hP.2.2.1
  have hρ' : 0 < P.βr * P.ρ := mul_pos hP.2.1 hP.2.2.2.1
  have hc : P.βr * P.ρ / P.βt * kap P = exp 1 := by
    have := hρ'.ne'; have := hβt.ne'
    unfold kap; field_simp; exact div_self hρ'.ne'
  have h : exp 1 ≤ P.βr * P.ρ / P.βt * d := by
    rw [← hc]; exact mul_le_mul_of_nonneg_left hd (by positivity)
  calc (1:ℝ) = Real.log (exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log (exp_pos 1) h

lemma profit_le_Phi (P : Params) (hP : Standing P) {p t : ℝ} (hf : Feasible P 1 (p, t)) :
    profit P p t 1 ≤ Phi P (dem P p t 1) := by
  obtain ⟨hp, ht, hcap⟩ := hf
  simp only at hp ht hcap
  have hY := hP.2.2.2.2.1
  have hω := omega_pos P hY zero_le_one le_rfl
  have hβt := hP.2.2.1
  have hρ' : 0 < P.βr * P.ρ := mul_pos hP.2.1 hP.2.2.2.1
  obtain ⟨hdem, hpr⟩ := plan_repr P hP (p := p) hω ht
  have hm := cap_margin P hP zero_le_one le_rfl hp ht
  have hk := kap_pos P hP
  have hl0 := (dem_fix P hP.1 (rho_nonneg P hP) (p := p) hω ht).1
  set D := idx P p t 1 with hD
  set l := dem P p t 1 with hl
  have hlog : Real.log l - Real.log (P.Λ - l) = D := by rw [hdem]; exact log_sig _ _ hP.1
  set d := P.μ - l with hd
  have hd0 : 0 < d := by linarith
  set c1 := P.βr * P.ρ / P.βt with hc1
  have hc1d : 0 < c1 * d := by positivity
  set Lg := Real.log (c1 * d) with hLg
  set E := Real.exp (-(d * t)) with hE
  have key : 1 - d * t + Lg ≤ E * (c1 * d) := by
    have := Real.add_one_le_exp (-(d * t) + Lg)
    rw [Real.exp_add, Real.exp_log hc1d] at this
    linarith
  have h2 : (1 + Lg) / d ≤ E * c1 + t := by
    rw [div_le_iff₀ hd0]; nlinarith
  have h3 : P.βt * (E * c1) = P.βr * P.ρ * E := by rw [hc1]; field_simp
  have hineq : P.βt * ((1 + Lg) / d) ≤ P.βr * P.ρ * E + P.βt * t := by
    have := mul_le_mul_of_nonneg_left h2 hβt.le
    nlinarith
  have hpe : p = P.α + P.βr * P.ρ * (1 - E) - P.βt * t - P.Ve - P.ωY * D := by
    rw [hpr]; unfold price; rw [omega_one P hY, ← hdem, hE, hd]; ring_nf
  have hPhi : Phi P l = l * (P.α - P.Ve - P.b - P.c + P.βr * P.ρ) -
      P.βt * (l * ((1 + Lg) / d)) - P.ωY * (l * D) := by
    unfold Phi cPhi; rw [hlog]
  rw [hPhi]
  show l * (p - P.b * 1 - P.c) ≤ _
  rw [hpe]
  nlinarith [mul_le_mul_of_nonneg_left hineq hl0.le]

lemma plan_of_l (P : Params) (hP : Standing P) {l : ℝ} (hl0 : 0 < l) (hlΛ : l < P.Λ)
    (hk : kap P ≤ P.μ - l) (hpos : 0 < Phi P l) :
    ∃ p t, Feasible P 1 (p, t) ∧ profit P p t 1 = Phi P l := by
  have hY := hP.2.2.2.2.1
  have hω := omega_pos P hY zero_le_one le_rfl
  have hβt := hP.2.2.1
  have hρ' : 0 < P.βr * P.ρ := mul_pos hP.2.1 hP.2.2.2.1
  have hkp := kap_pos P hP
  have hb := hP.2.2.2.2.2.2.1
  have hL1 : 1 ≤ Real.log (P.βr * P.ρ / P.βt * (P.μ - l)) := log_ge_one P hP hk
  set d := P.μ - l with hd
  have hd0 : 0 < d := by linarith
  have hdne : d ≠ 0 := hd0.ne'
  set Lg := Real.log (P.βr * P.ρ / P.βt * d) with hLg
  set D := Real.log l - Real.log (P.Λ - l) with hD
  have ht : 0 ≤ Lg / d := div_nonneg (by linarith) hd0.le
  have hdem : dem P (price P 1 D (Lg / d)) (Lg / d) 1 = l := by
    rw [dem_price P hP hω ht D]; exact sig_log hl0 hlΛ
  have hexp : Real.exp (-(P.μ - P.Λ * sigmoid D) * (Lg / d)) = P.βt / (P.βr * P.ρ * d) := by
    rw [sig_log hl0 hlΛ, ← hd]
    have : -d * (Lg / d) = -Lg := by field_simp
    rw [this, Real.exp_neg, hLg, Real.exp_log (by positivity)]
    field_simp
  have hprof : profit P (price P 1 D (Lg / d)) (Lg / d) 1 = Phi P l := by
    unfold profit; rw [hdem]
    unfold price; rw [hexp, omega_one P hY]
    unfold Phi cPhi
    rw [← hD, ← hd, ← hLg]
    have := hP.2.1.ne'; have := hP.2.2.2.1.ne'; have := hβt.ne'
    field_simp
    ring
  refine ⟨_, _, ⟨?_, ht, ?_⟩, hprof⟩
  · show P.c ≤ price P 1 D (Lg / d)
    have h1 : 0 < profit P (price P 1 D (Lg / d)) (Lg / d) 1 := hprof ▸ hpos
    unfold profit at h1; rw [hdem] at h1
    have key : 0 < price P 1 D (Lg / d) - P.b * 1 - P.c := by
      by_contra hcon; push Not at hcon
      have := mul_nonpos_of_nonneg_of_nonpos hl0.le hcon
      linarith
    linarith
  · show 1 ≤ (P.μ - dem P (price P 1 D (Lg / d)) (Lg / d) 1) * (Lg / d)
    rw [hdem, ← hd]
    have : d * (Lg / d) = Lg := by field_simp
    rw [this]; exact hL1

lemma no_two (P : Params) (hP : Standing P) {l1 l2 : ℝ} (h12 : l1 < l2) (hl1 : 0 < l1)
    (hl2 : l2 < P.Λ) (hk : kap P ≤ P.μ - l2)
    (h1 : optProfit P 1 ≤ Phi P l1) (h2 : optProfit P 1 ≤ Phi P l2) : False := by
  have hβt := hP.2.2.1
  have hρ' : 0 < P.βr * P.ρ := mul_pos hP.2.1 hP.2.2.2.1
  have hkp := kap_pos P hP
  have hconc := conc_gen (P.α - P.Ve - P.b - P.c + P.βr * P.ρ) P.βt (P.βr * P.ρ / P.βt) P.μ P.Λ
    P.ωY l1 l2 hβt (by positivity) hP.2.2.2.2.1 hl1 h12 hl2 (by linarith) (log_ge_one P hP hk)
  have hmid := hconc.2 ⟨le_rfl, h12.le⟩ ⟨h12.le, le_rfl⟩ h12.ne (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have hg0 := optProfit_nonneg P hP zero_le_one le_rfl
  unfold Phi at h1 h2
  have hPm : 0 < Phi P (1 / 2 * l1 + 1 / 2 * l2) := by unfold Phi; linarith
  obtain ⟨p, t, hf, hpr⟩ := plan_of_l P hP (l := 1 / 2 * l1 + 1 / 2 * l2) (by linarith)
    (by linarith) (by linarith) hPm
  have := le_optProfit P hP zero_le_one le_rfl hf
  unfold Phi at hpr
  linarith

lemma uniq1 (P : Params) (hP : Standing P) {x y : ℝ × ℝ} (hx : IsOptimal P 1 x)
    (hy : IsOptimal P 1 y) : dem P x.1 x.2 1 = dem P y.1 y.2 1 := by
  have hω := omega_pos P hP.2.2.2.2.1 zero_le_one le_rfl
  have hgx := opt_eq P hP zero_le_one le_rfl hx
  have hgy := opt_eq P hP zero_le_one le_rfl hy
  have hbx := profit_le_Phi P hP (p := x.1) (t := x.2) hx.1
  have hby := profit_le_Phi P hP (p := y.1) (t := y.2) hy.1
  rw [← hgx] at hbx
  rw [← hgy] at hby
  obtain ⟨hx0, hxΛ, -⟩ := dem_fix P hP.1 (rho_nonneg P hP) (p := x.1) hω hx.1.2.1
  obtain ⟨hy0, hyΛ, -⟩ := dem_fix P hP.1 (rho_nonneg P hP) (p := y.1) hω hy.1.2.1
  have hkx := cap_margin P hP zero_le_one le_rfl hx.1.1 hx.1.2.1
  have hky := cap_margin P hP zero_le_one le_rfl hy.1.1 hy.1.2.1
  rcases lt_trichotomy (dem P x.1 x.2 1) (dem P y.1 y.2 1) with h | h | h
  · exact (no_two P hP h hx0 hyΛ hky hbx hby).elim
  · exact h
  · exact (no_two P hP h hy0 hxΛ hkx hby hbx).elim

lemma transport_plan (P : Params) (hP : Standing P) {ϕ1 ϕ2 p t : ℝ} (h1 : ϕ1 ∈ Icc (0:ℝ) 1)
    (h2 : ϕ2 ∈ Icc (0:ℝ) 1) (ht : 0 ≤ t) :
    dem P (p + (ωθ P ϕ1 - ωθ P ϕ2) * idx P p t ϕ1) t ϕ2 = dem P p t ϕ1 ∧
    idx P (p + (ωθ P ϕ1 - ωθ P ϕ2) * idx P p t ϕ1) t ϕ2 = idx P p t ϕ1 ∧
    profit P (p + (ωθ P ϕ1 - ωθ P ϕ2) * idx P p t ϕ1) t ϕ2 =
      profit P p t ϕ1 + dem P p t ϕ1 * ((ωθ P ϕ1 - ωθ P ϕ2) * idx P p t ϕ1 - P.b * (ϕ2 - ϕ1)) := by
  have hΛ := hP.1
  have hρ' := rho_nonneg P hP
  have hω1 := omega_pos P hP.2.2.2.2.1 h1.1 h1.2
  have hω2 := omega_pos P hP.2.2.2.2.1 h2.1 h2.2
  obtain ⟨hl0, hlΛ, hfix⟩ := dem_fix P hΛ hρ' (p := p) hω1 ht
  set l := dem P p t ϕ1 with hl
  set D := idx P p t ϕ1 with hD
  set p2 := p + (ωθ P ϕ1 - ωθ P ϕ2) * D with hp2
  have e2 : Vdet P p t l - P.Ve = ωθ P ϕ1 * D := by rw [hD, idx, ← hl]; field_simp
  have hV2 : Vdet P p2 t l - P.Ve = ωθ P ϕ2 * D := by
    have e1 : Vdet P p2 t l = Vdet P p t l - (ωθ P ϕ1 - ωθ P ϕ2) * D := by
      unfold Vdet; rw [hp2]; ring
    rw [e1]; linarith
  have hfix2 : l = P.Λ * sigmoid ((Vdet P p2 t l - P.Ve) / ωθ P ϕ2) := by
    rw [hV2, mul_div_cancel_left₀ _ hω2.ne', hD, idx, ← hl]; exact hfix
  have hd2 : dem P p2 t ϕ2 = l := dem_eq_of_fix P hΛ hρ' hω2 ht hl0.le hlΛ.le hfix2
  refine ⟨hd2, ?_, ?_⟩
  · unfold idx; rw [hd2, hV2, mul_div_cancel_left₀ _ hω2.ne']
  · unfold profit; rw [hd2, ← hl, hp2]; ring

lemma sig_mul_ge (D : ℝ) : -1 ≤ sigmoid D * D := by
  rcases le_or_gt 0 D with h | h
  · have := sigmoid_pos D; nlinarith
  · have h1 := sigmoid_le_exp D
    have h2 : -D ≤ exp (-D) := by have := Real.add_one_le_exp (-D); linarith
    have h3 : exp D * exp (-D) = 1 := by rw [← exp_add]; simp
    have h4 := exp_pos D
    have h5 : sigmoid D * (-D) ≤ exp D * (-D) := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h6 : exp D * (-D) ≤ exp D * exp (-D) := mul_le_mul_of_nonneg_left h2 h4.le
    nlinarith

open Filter Topology in
lemma nearH (P : Params) (hP : Standing P)
    (hcon : ∀ c ∈ Ico (0:ℝ) 1, optProfit P 1 ≤ optProfit P c) {τ : ℝ}
    (hτ : P.b * P.ωY / P.βr ^ 2 < τ) {η : ℝ} (hη : 0 < η) (hηg : η ≤ optProfit P 1) :
    ∃ p t, Feasible P 1 (p, t) ∧ idx P p t 1 ≤ τ ∧ optProfit P 1 - η < profit P p t 1 := by
  have hY := hP.2.2.2.2.1
  have hb := hP.2.2.2.2.2.2.1
  have hΛ := hP.1
  have hβ : 0 < P.βr ^ 2 := by have := hP.2.1; positivity
  have hτ' : P.b * P.ωY < τ * P.βr ^ 2 := by rwa [div_lt_iff₀ hβ] at hτ
  have hc1 : Continuous (fun ϕ : ℝ => τ * P.βr ^ 2 * (1 + ϕ) - P.b * (ωθ P ϕ + P.ωY)) := by
    unfold ωθ; fun_prop
  have hc2 : Continuous (fun ϕ : ℝ => P.Λ * (ωθ P ϕ - P.ωY) + P.Λ * P.b * (1 - ϕ)) := by
    unfold ωθ; fun_prop
  have e1 : 0 < τ * P.βr ^ 2 * (1 + 1) - P.b * (ωθ P 1 + P.ωY) := by
    rw [omega_one P hY]; linarith
  have e2 : P.Λ * (ωθ P 1 - P.ωY) + P.Λ * P.b * (1 - 1) < η := by
    rw [omega_one P hY]; simp; exact hη
  have ev1 := (hc1.tendsto 1).eventually (lt_mem_nhds e1)
  have ev2 := (hc2.tendsto 1).eventually (gt_mem_nhds e2)
  have ev3 : ∀ᶠ ϕ in 𝓝 (1:ℝ), (0:ℝ) < ϕ := lt_mem_nhds (by norm_num)
  have ev : ∀ᶠ ϕ in 𝓝[<] (1:ℝ), ((0 < τ * P.βr ^ 2 * (1 + ϕ) - P.b * (ωθ P ϕ + P.ωY) ∧
      P.Λ * (ωθ P ϕ - P.ωY) + P.Λ * P.b * (1 - ϕ) < η) ∧ (0:ℝ) < ϕ) ∧ ϕ ∈ Iio 1 :=
    (((ev1.and ev2).and ev3).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ϕ, ⟨⟨hC1, hC2⟩, hϕ0⟩, hϕ1⟩ := ev.exists
  have hϕ1' : ϕ < 1 := hϕ1
  have hϕI : ϕ ∈ Icc (0:ℝ) 1 := ⟨hϕ0.le, hϕ1'.le⟩
  have h1I : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨⟨p, t⟩, hopt⟩ := hex P hP ϕ hϕI
  have hG := opt_eq P hP hϕ0.le hϕ1'.le hopt
  simp only at hG
  have hgle := hcon ϕ ⟨hϕ0.le, hϕ1'⟩
  have htr := transport P hP hϕI h1I hopt.1
  obtain ⟨hd2, hi2, hpr2⟩ := transport_plan P hP (p := p) hϕI h1I hopt.1.2.1
  rw [← hG] at htr hpr2
  rw [omega_one P hY] at htr hd2 hi2 hpr2
  have hω := omega_pos P hY hϕ0.le hϕ1'.le
  obtain ⟨hl0, hlΛ, -⟩ := dem_fix P hΛ (rho_nonneg P hP) (p := p) hω hopt.1.2.1
  obtain ⟨hdem, -⟩ := plan_repr P hP (p := p) hω hopt.1.2.1
  have hsq := omega_sq P hϕ0.le hϕ1'.le
  have hwY := omega_lt P hP hϕ0.le hϕ1' le_rfl
  rw [omega_one P hY] at hwY
  set l := dem P p t ϕ with hl
  set D := idx P p t ϕ with hD
  set w := ωθ P ϕ with hw
  have hA : (w - P.ωY) * D ≤ P.b * (1 - ϕ) := by
    have hneg : l * ((w - P.ωY) * D - P.b * (1 - ϕ)) ≤ 0 := by linarith
    by_contra hc; push Not at hc
    have : 0 < l * ((w - P.ωY) * D - P.b * (1 - ϕ)) := mul_pos hl0 (by linarith)
    linarith
  have hDτ : D ≤ τ := by
    by_contra hc; push Not at hc
    have i1 : (w - P.ωY) * τ ≤ P.b * (1 - ϕ) :=
      le_trans (mul_le_mul_of_nonneg_left hc.le (by linarith)) hA
    have e : (w - P.ωY) * (w + P.ωY) = P.βr ^ 2 * (1 - ϕ) * (1 + ϕ) := by
      linear_combination hsq
    have i2 : (1 - ϕ) * (P.βr ^ 2 * (1 + ϕ) * τ) ≤ (1 - ϕ) * (P.b * (w + P.ωY)) := by
      have := mul_le_mul_of_nonneg_right i1 (show 0 ≤ w + P.ωY by linarith)
      have e2 : (w - P.ωY) * τ * (w + P.ωY) = (1 - ϕ) * (P.βr ^ 2 * (1 + ϕ) * τ) := by
        linear_combination τ * e
      have e3 : P.b * (1 - ϕ) * (w + P.ωY) = (1 - ϕ) * (P.b * (w + P.ωY)) := by ring
      rw [e2, e3] at this; exact this
    have i3 := le_of_mul_le_mul_left i2 (by linarith)
    linarith
  have hlD : -P.Λ ≤ l * D := by
    rw [hdem]
    have := sig_mul_ge D
    have := mul_le_mul_of_nonneg_left this hΛ.le
    linarith
  have hwY0 : 0 ≤ w - P.ωY := by linarith
  have hlow : optProfit P 1 - η < optProfit P ϕ + l * ((w - P.ωY) * D - P.b * (1 - ϕ)) := by
    have i1 : -(P.Λ * (w - P.ωY)) ≤ (w - P.ωY) * (l * D) := by
      have := mul_le_mul_of_nonneg_left hlD hwY0
      linarith
    have i2 : l * (P.b * (1 - ϕ)) ≤ P.Λ * P.b * (1 - ϕ) := by
      have : 0 ≤ P.b * (1 - ϕ) := mul_nonneg hb.le (by linarith)
      have := mul_le_mul_of_nonneg_right hlΛ.le this
      linarith
    linarith
  refine ⟨p + (w - P.ωY) * D, t, ⟨?_, hopt.1.2.1, ?_⟩, ?_, ?_⟩
  · show P.c ≤ p + (w - P.ωY) * D
    have hpos : 0 < profit P (p + (w - P.ωY) * D) t 1 := by rw [hpr2]; linarith
    unfold profit at hpos; rw [hd2] at hpos
    have key : 0 < p + (w - P.ωY) * D - P.b * 1 - P.c := by
      by_contra hcon'; push Not at hcon'
      have := mul_nonpos_of_nonneg_of_nonpos hl0.le hcon'
      linarith
    linarith
  · show 1 ≤ (P.μ - dem P (p + (w - P.ωY) * D) t 1) * t
    rw [hd2]; exact hopt.1.2.2
  · rw [hi2]; exact hDτ
  · rw [hpr2]; exact hlow

theorem stepH (P : Params) (hP : Standing P) (h23 : ¬ cond23 P) :
    ∃ c ∈ Ico (0:ℝ) 1, optProfit P c < optProfit P 1 := by
  by_contra hne
  push Not at hne
  have hY := hP.2.2.2.2.1
  have hβ : 0 < P.βr ^ 2 := by have := hP.2.1; positivity
  have h1I : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hopt1 := optPlan_spec P (hex P hP 1 h1I)
  have hD : idx P (optPlan P 1).1 (optPlan P 1).2 1 = (optV P 1 - P.Ve) / P.ωY := by
    unfold idx optV optDem; rw [omega_one P hY]
  have h23' : P.b * P.ωY ^ 2 / P.βr ^ 2 < optV P 1 - P.Ve := by
    unfold cond23 at h23; push Not at h23; exact h23
  have hτ0 : P.b * P.ωY / P.βr ^ 2 < idx P (optPlan P 1).1 (optPlan P 1).2 1 := by
    rw [hD, lt_div_iff₀ hY]
    calc P.b * P.ωY / P.βr ^ 2 * P.ωY = P.b * P.ωY ^ 2 / P.βr ^ 2 := by ring
      _ < _ := h23'
  set D1 := idx P (optPlan P 1).1 (optPlan P 1).2 1 with hD1
  set τ := (P.b * P.ωY / P.βr ^ 2 + D1) / 2 with hτ
  have hτa : P.b * P.ωY / P.βr ^ 2 < τ := by linarith
  have hτb : τ < D1 := by linarith
  obtain ⟨hf0, hp0⟩ := pos_plan P hP zero_le_one le_rfl
  have hg1 : 0 < optProfit P 1 := hp0.trans_le (le_optProfit P hP zero_le_one le_rfl hf0)
  obtain ⟨pg, tg, hfg, hig, hpg⟩ := nearH P hP hne hτa hg1 le_rfl
  have hgood : ∃ p t, Feasible P 1 (p, t) ∧ idx P p t 1 ≤ τ ∧ 0 < profit P p t 1 :=
    ⟨pg, tg, hfg, hig, by linarith⟩
  obtain ⟨py, ty, hfy, hiy, hmax⟩ := exists_opt P hP zero_le_one le_rfl τ hgood
  have hvpos : 0 < profit P py ty 1 := lt_of_lt_of_le (by linarith) (hmax pg tg hfg hig)
  by_cases hv : optProfit P 1 ≤ profit P py ty 1
  · have hoy : IsOptimal P 1 (py, ty) :=
      ⟨hfy, fun z hz => (le_optProfit P hP zero_le_one le_rfl hz).trans hv⟩
    have hu := uniq1 P hP hopt1 hoy
    have hω := omega_pos P hY zero_le_one le_rfl
    have r1 := (plan_repr P hP (p := (optPlan P 1).1) hω hopt1.1.2.1).1
    have r2 := (plan_repr P hP (p := py) hω hfy.2.1).1
    simp only at hu
    rw [r1, r2] at hu
    have hs := Real.sigmoid_injective (mul_left_cancel₀ hP.1.ne' hu)
    linarith
  · push Not at hv
    obtain ⟨p3, t3, hf3, hi3, hp3⟩ := nearH P hP hne hτa (η := optProfit P 1 - profit P py ty 1)
      (by linarith) (by linarith)
    have := hmax p3 t3 hf3 hi3
    linarith

end DD4690

open DeliveryDisclosure.InfoEffort in
theorem solution (P : Params) (hP : Standing P) :
    (cond23 P → StrictAntiOn (optProfit P) (Set.Icc 0 1)) ∧
      (¬ cond23 P → ∃ ϕ0 ∈ Set.Ioo (0 : ℝ) 1,
        StrictAntiOn (optProfit P) (Set.Icc 0 ϕ0) ∧ StrictMonoOn (optProfit P) (Set.Icc ϕ0 1)) ∧
      ∀ ϕ ∈ Set.Ioo (0 : ℝ) 1, optProfit P ϕ < max (optProfit P 0) (optProfit P 1) := by
  exact DD4690.main_of_H P hP (DD4690.stepH P hP)
