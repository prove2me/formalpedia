-- Prove2me | solution 1 for BIInsurance.Screening.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:03:07.684863+00:00
-- url     : https://prove2.me/submissions/23206bb4-9e0f-4341-8e51-411326c6c426

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model
import Theorems.Thm_BIInsurance_Screening_eq_4_1

open Set Filter Topology

namespace BIInsurance.Screening.P4

open BIInsurance.Screening

/-- Averaged scenario cost `c e*K + A L(e*)` as a function of the early forecast `mu`
and of `a = A(s)`. -/
noncomputable def GG (P : Params) (mu a : ℝ) : ℝ :=
  P.c * (mu + P.γ * (Real.log (a - P.c) - Real.log P.c))
    + a * (P.K - P.γ * Exi P mu - P.γ * Real.log (a - P.c) + P.γ * Real.log a)

noncomputable def QQ (P : Params) (mu : ℝ) : ℝ :=
  (P.T : ℝ) * P.p * (P.β * sales P (mu + P.dH) P.K + (1 - P.β) * sales P (mu + P.dL) P.K)

lemma EpiI_y (P : Params) (mu y s : ℝ) : EpiI P mu y s = EpiI P mu 0 s - y := by
  unfold EpiI piI1e piI0; ring

lemma Aeff_bounds (P : Params) (hS : P.Standing) (s : ℝ) (hs : s ∈ Icc 0 P.sbar) :
    P.c < Aeff P s ∧ Aeff P s ≤ ((P.T : ℝ) - P.τ) * P.p := by
  obtain ⟨hτ, hK, hmuL, hmuLH, hdL, hdH, hβ0, hβ1, hβd, hα0, hα1, hγ, hρ0, hρ1, hlam, hp, hc,
    hcT, hw, hsb0, hsb⟩ := hS
  obtain ⟨hs0, hs1⟩ := hs
  have hTp : 0 < ((P.T : ℝ) - P.τ) * P.p := lt_of_lt_of_le hc hcT
  have hE : 0 < Real.exp (-(P.muL + P.dL) / P.γ) := Real.exp_pos _
  have h1 : P.c / (((P.T : ℝ) - P.τ) * P.p) < 1 - P.sbar := by
    have : P.c / (((P.T : ℝ) - P.τ) * P.p) <
        P.c / (((P.T : ℝ) - P.τ) * P.p) * (1 + Real.exp (-(P.muL + P.dL) / P.γ)) := by
      have : 0 < P.c / (((P.T : ℝ) - P.τ) * P.p) := div_pos hc hTp
      nlinarith
    linarith
  have h2 : P.c < (1 - P.sbar) * (((P.T : ℝ) - P.τ) * P.p) := by
    rwa [div_lt_iff₀ hTp] at h1
  have hw0 : (0 : ℝ) ≤ P.w := Nat.cast_nonneg _
  have hTw : 0 < (P.T : ℝ) - P.τ - P.w := by linarith
  unfold Aeff
  constructor
  · have : (1 - P.sbar) * (((P.T : ℝ) - P.τ) * P.p) ≤ (P.w : ℝ) * P.p
        + ((P.T : ℝ) - P.τ - P.w) * P.p * (1 - s) := by
      have e1 : (1 - P.sbar) * (((P.T : ℝ) - P.τ) * P.p) ≤ (1 - s) * (((P.T : ℝ) - P.τ) * P.p) :=
        mul_le_mul_of_nonneg_right (by linarith) hTp.le
      have e2 : 0 ≤ (P.w : ℝ) * P.p * s := by positivity
      nlinarith
    linarith
  · have : 0 ≤ ((P.T : ℝ) - P.τ - P.w) * P.p * s := by positivity
    nlinarith

lemma eStar_int (P : Params) (hS : P.Standing) (hKc : KCond P) (m s : ℝ)
    (hm : m ≤ P.muH + P.dH) (hs : s ∈ Icc 0 P.sbar) :
    eStar P m s * P.K = m + P.γ * (Real.log (Aeff P s - P.c) - Real.log P.c) := by
  have hA := Aeff_bounds P hS s hs
  have hK : 0 < P.K := hS.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hc : 0 < P.c := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlog : Real.log ((Aeff P s - P.c) / P.c) ≤ Real.log ((((P.T : ℝ) - P.τ) * P.p - P.c) / P.c) := by
    apply Real.log_le_log (div_pos (by linarith [hA.1]) hc)
    exact div_le_div_of_nonneg_right (by linarith [hA.2]) hc.le
  have hlt : m + P.γ * Real.log ((Aeff P s - P.c) / P.c) < P.K := by
    unfold KCond at hKc
    have := mul_le_mul_of_nonneg_left hlog hγ.le
    linarith
  unfold eStar
  rw [if_pos hlt, div_mul_cancel₀ _ hK.ne', Real.log_div (by linarith [hA.1]) hc.ne']

lemma sales_eq (P : Params) (hS : P.Standing) (m x : ℝ) :
    sales P m x = x + m - P.γ * Real.log (Real.exp (x / P.γ) + Real.exp (m / P.γ)) :=
  (eq_4_1 P.γ m x hS.2.2.2.2.2.2.2.2.2.2.2.1).2

lemma lost_star (P : Params) (hS : P.Standing) (hKc : KCond P) (m s : ℝ)
    (hm : m ≤ P.muH + P.dH) (hs : s ∈ Icc 0 P.sbar) :
    lostSales P m (eStar P m s) = P.K - P.γ * Real.log (Real.exp (P.K / P.γ) + Real.exp (m / P.γ))
      - P.γ * Real.log (Aeff P s - P.c) + P.γ * Real.log (Aeff P s) := by
  have hA := Aeff_bounds P hS s hs
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hc : 0 < P.c := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAc : 0 < Aeff P s - P.c := by linarith [hA.1]
  have hApos : 0 < Aeff P s := by linarith [hA.1]
  unfold lostSales
  rw [eStar_int P hS hKc m s hm hs, sales_eq P hS, sales_eq P hS]
  have hx : Real.exp ((m + P.γ * (Real.log (Aeff P s - P.c) - Real.log P.c)) / P.γ)
      + Real.exp (m / P.γ) = Real.exp (m / P.γ) * (Aeff P s / P.c) := by
    have : (m + P.γ * (Real.log (Aeff P s - P.c) - Real.log P.c)) / P.γ
        = m / P.γ + Real.log ((Aeff P s - P.c) / P.c) := by
      rw [Real.log_div hAc.ne' hc.ne']; field_simp
    rw [this, Real.exp_add, Real.exp_log (div_pos hAc hc)]
    field_simp; ring
  rw [hx, Real.log_mul (Real.exp_pos _).ne' (div_pos hApos hc).ne', Real.log_exp,
    Real.log_div hApos.ne' hc.ne']
  field_simp
  ring

lemma piI1e_eq (P : Params) (m e y s : ℝ) :
    piI1e P m e y s = -y + (P.T : ℝ) * P.p * sales P m P.K
      - (1 + P.lam) * (P.c * (e * P.K) + Aeff P s * lostSales P m e) := by
  unfold piI1e Aeff lostSales; ring

lemma scen_eq (P : Params) (hS : P.Standing) (hKc : KCond P) (m y s : ℝ)
    (hm : m ≤ P.muH + P.dH) (hs : s ∈ Icc 0 P.sbar) :
    P.ρ * piI1e P m (eStar P m s) y s + (1 - P.ρ) * piI0 P m y
      = -y + (P.T : ℝ) * P.p * sales P m P.K
        - P.ρ * (1 + P.lam) * (P.c * (m + P.γ * (Real.log (Aeff P s - P.c) - Real.log P.c))
          + Aeff P s * (P.K - P.γ * Real.log (Real.exp (P.K / P.γ) + Real.exp (m / P.γ))
            - P.γ * Real.log (Aeff P s - P.c) + P.γ * Real.log (Aeff P s))) := by
  rw [piI1e_eq, eStar_int P hS hKc m s hm hs, lost_star P hS hKc m s hm hs]
  unfold piI0; ring

lemma EpiI_formula (P : Params) (hS : P.Standing) (hKc : KCond P) (mu y s : ℝ)
    (hmu : mu ≤ P.muH) (hs : s ∈ Icc 0 P.sbar) :
    EpiI P mu y s = -y + QQ P mu - P.ρ * (1 + P.lam) * GG P mu (Aeff P s) := by
  have hdL : P.dL < 0 := hS.2.2.2.2.1
  have hdH : 0 < P.dH := hS.2.2.2.2.2.1
  have hβd : P.β * P.dH + (1 - P.β) * P.dL = 0 := hS.2.2.2.2.2.2.2.2.1
  unfold EpiI
  rw [scen_eq P hS hKc _ y s (by linarith) hs, scen_eq P hS hKc _ y s (by linarith) hs]
  unfold QQ GG Exi xi
  linear_combination (-(P.ρ * (1 + P.lam) * P.c)) * hβd

lemma Exi_lt (P : Params) (hS : P.Standing) : Exi P P.muL < Exi P P.muH := by
  have hmu : P.muL < P.muH := hS.2.2.2.1
  have hβ0 : 0 < P.β := hS.2.2.2.2.2.2.1
  have hβ1 : P.β < 1 := hS.2.2.2.2.2.2.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have key : ∀ d : ℝ, xi P P.K P.muL d < xi P P.K P.muH d := by
    intro d
    unfold xi
    apply Real.log_lt_log (by positivity)
    have : (P.muL + d) / P.γ < (P.muH + d) / P.γ := by
      apply div_lt_div_of_pos_right _ hγ; linarith
    have := Real.exp_lt_exp.mpr this
    linarith
  unfold Exi
  have h1 := key P.dH
  have h2 := key P.dL
  nlinarith

lemma Aeff_sub (P : Params) (a b : ℝ) :
    Aeff P a - Aeff P b = ((P.T : ℝ) - P.τ - P.w) * P.p * (b - a) := by
  unfold Aeff; ring

/-- `V_H(s) - V_L(s)` changes linearly in `A(s)`. -/
lemma D_diff (P : Params) (hS : P.Standing) (hKc : KCond P) (a b : ℝ)
    (ha : a ∈ Icc 0 P.sbar) (hb : b ∈ Icc 0 P.sbar) :
    (EpiI P P.muH 0 a - EpiI P P.muL 0 a) - (EpiI P P.muH 0 b - EpiI P P.muL 0 b)
      = P.ρ * (1 + P.lam) * P.γ * (Exi P P.muH - Exi P P.muL)
          * (((P.T : ℝ) - P.τ - P.w) * P.p * (b - a)) := by
  have hmu : P.muL ≤ P.muH := hS.2.2.2.1.le
  rw [EpiI_formula P hS hKc _ 0 a hmu ha, EpiI_formula P hS hKc _ 0 a le_rfl ha,
    EpiI_formula P hS hKc _ 0 b hmu hb, EpiI_formula P hS hKc _ 0 b le_rfl hb, ← Aeff_sub]
  unfold GG; ring

lemma D_strict (P : Params) (hS : P.Standing) (hKc : KCond P) (a b : ℝ)
    (ha : a ∈ Icc 0 P.sbar) (hb : b ∈ Icc 0 P.sbar) (hab : a < b) :
    EpiI P P.muH 0 b - EpiI P P.muL 0 b < EpiI P P.muH 0 a - EpiI P P.muL 0 a := by
  have h := D_diff P hS hKc a b ha hb
  have hρ : 0 < P.ρ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlam : 0 < P.lam := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : 0 < P.p := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw : (P.w : ℝ) < (P.T : ℝ) - P.τ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hE := Exi_lt P hS
  have : 0 < P.ρ * (1 + P.lam) * P.γ * (Exi P P.muH - Exi P P.muL)
          * (((P.T : ℝ) - P.τ - P.w) * P.p * (b - a)) := by
    apply mul_pos
    · apply mul_pos (mul_pos (mul_pos hρ (by linarith)) hγ) (by linarith)
    · apply mul_pos (mul_pos (by linarith) hp) (by linarith)
  linarith

lemma D_anti (P : Params) (hS : P.Standing) (hKc : KCond P) (a b : ℝ)
    (ha : a ∈ Icc 0 P.sbar) (hb : b ∈ Icc 0 P.sbar) (hab : a ≤ b) :
    EpiI P P.muH 0 b - EpiI P P.muL 0 b ≤ EpiI P P.muH 0 a - EpiI P P.muL 0 a := by
  rcases hab.lt_or_eq with h | h
  · exact (D_strict P hS hKc a b ha hb h).le
  · rw [h]

lemma GG_hasDerivAt (P : Params) (mu a : ℝ) (hc : 0 < P.c) (ha : P.c < a) :
    HasDerivAt (GG P mu)
      (P.K - P.γ * Exi P mu + P.γ * (Real.log a - Real.log (a - P.c))) a := by
  have hac : a - P.c ≠ 0 := by linarith
  have ha0 : a ≠ 0 := by linarith
  have h1 : HasDerivAt (fun a => Real.log (a - P.c)) (1 / (a - P.c)) a := by
    have := ((hasDerivAt_id a).sub_const P.c).log hac
    simpa using this
  have h2 : HasDerivAt (fun a => Real.log a) (1 / a) a := by
    simpa using Real.hasDerivAt_log ha0
  have hG := (((h1.sub_const (Real.log P.c)).const_mul P.γ).const_add mu).const_mul P.c |>.add
    ((hasDerivAt_id a).mul ((((h1.const_mul P.γ).const_sub
      (P.K - P.γ * Exi P mu)).add (h2.const_mul P.γ))))
  unfold GG
  refine hG.congr_deriv ?_
  simp only [id, Pi.add_apply]
  field_simp
  ring

lemma xi_bound (P : Params) (hγ : 0 < P.γ) (hc : 0 < P.c) (m a : ℝ) (ha : P.c < a)
    (hint : m + P.γ * (Real.log (a - P.c) - Real.log P.c) < P.K) :
    P.γ * Real.log (Real.exp (P.K / P.γ) + Real.exp (m / P.γ))
      < P.K + P.γ * (Real.log a - Real.log (a - P.c)) := by
  have hac : 0 < a - P.c := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : m / P.γ < P.K / P.γ + Real.log (P.c / (a - P.c)) := by
    rw [Real.log_div hc.ne' hac.ne', div_lt_iff₀ hγ]
    have : (P.K / P.γ + (Real.log P.c - Real.log (a - P.c))) * P.γ
        = P.K + P.γ * (Real.log P.c - Real.log (a - P.c)) := by field_simp
    rw [this]; linarith
  have h2 : Real.exp (m / P.γ) < Real.exp (P.K / P.γ) * (P.c / (a - P.c)) := by
    have := Real.exp_lt_exp.mpr h1
    rwa [Real.exp_add, Real.exp_log (div_pos hc hac)] at this
  have h3 : Real.exp (P.K / P.γ) + Real.exp (m / P.γ) < Real.exp (P.K / P.γ) * (a / (a - P.c)) := by
    have : Real.exp (P.K / P.γ) * (a / (a - P.c))
        = Real.exp (P.K / P.γ) + Real.exp (P.K / P.γ) * (P.c / (a - P.c)) := by
      field_simp; ring
    linarith
  have h4 := Real.log_lt_log (by positivity) h3
  rw [Real.log_mul (Real.exp_pos _).ne' (div_pos ha0 hac).ne', Real.log_exp,
    Real.log_div ha0.ne' hac.ne'] at h4
  have := mul_lt_mul_of_pos_left h4 hγ
  have e : P.γ * (P.K / P.γ + (Real.log a - Real.log (a - P.c)))
      = P.K + P.γ * (Real.log a - Real.log (a - P.c)) := by field_simp
  linarith

lemma GG_deriv_pos (P : Params) (hS : P.Standing) (hKc : KCond P) (a : ℝ) (ha : P.c < a)
    (ha' : a ≤ ((P.T : ℝ) - P.τ) * P.p) :
    0 < P.K - P.γ * Exi P P.muH + P.γ * (Real.log a - Real.log (a - P.c)) := by
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hc : 0 < P.c := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdL : P.dL < 0 := hS.2.2.2.2.1
  have hdH : 0 < P.dH := hS.2.2.2.2.2.1
  have hβ0 : 0 < P.β := hS.2.2.2.2.2.2.1
  have hβ1 : P.β < 1 := hS.2.2.2.2.2.2.2.1
  have hlog : Real.log ((a - P.c) / P.c) ≤ Real.log ((((P.T : ℝ) - P.τ) * P.p - P.c) / P.c) := by
    apply Real.log_le_log (div_pos (by linarith) hc)
    exact div_le_div_of_nonneg_right (by linarith) hc.le
  rw [Real.log_div (by linarith) hc.ne'] at hlog
  have hint : ∀ m, m ≤ P.muH + P.dH → m + P.γ * (Real.log (a - P.c) - Real.log P.c) < P.K := by
    intro m hm
    unfold KCond at hKc
    have := mul_le_mul_of_nonneg_left hlog hγ.le
    linarith
  have bH := xi_bound P hγ hc (P.muH + P.dH) a ha (hint _ le_rfl)
  have bL := xi_bound P hγ hc (P.muH + P.dL) a ha (hint _ (by linarith))
  unfold Exi xi
  nlinarith

lemma VH_mono (P : Params) (hS : P.Standing) (hKc : KCond P) (a b : ℝ)
    (ha : a ∈ Icc 0 P.sbar) (hb : b ∈ Icc 0 P.sbar) (hab : a ≤ b) :
    EpiI P P.muH 0 a ≤ EpiI P P.muH 0 b := by
  have hc : 0 < P.c := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hρ : 0 < P.ρ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlam : 0 < P.lam := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : 0 < P.p := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw : (P.w : ℝ) < (P.T : ℝ) - P.τ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set D := Ioc P.c (((P.T : ℝ) - P.τ) * P.p) with hD
  have hmono : MonotoneOn (GG P P.muH) D := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro x hx
      exact (GG_hasDerivAt P P.muH x hc hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (GG_hasDerivAt P P.muH x hc hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(GG_hasDerivAt P P.muH x hc hx.1).deriv]
      exact (GG_deriv_pos P hS hKc x hx.1 hx.2.le).le
  have hAa := Aeff_bounds P hS a ha
  have hAb := Aeff_bounds P hS b hb
  have hle : Aeff P b ≤ Aeff P a := by
    have := Aeff_sub P a b
    have : 0 ≤ ((P.T : ℝ) - P.τ - P.w) * P.p * (b - a) :=
      mul_nonneg (mul_nonneg (by linarith) hp.le) (by linarith)
    linarith
  have hG := hmono ⟨hAb.1, hAb.2⟩ ⟨hAa.1, hAa.2⟩ hle
  rw [EpiI_formula P hS hKc _ 0 a le_rfl ha, EpiI_formula P hS hKc _ 0 b le_rfl hb]
  have : 0 < P.ρ * (1 + P.lam) := mul_pos hρ (by linarith)
  nlinarith

lemma claimCost_formula (P : Params) (hS : P.Standing) (hKc : KCond P) (mu s : ℝ)
    (hmu : mu ≤ P.muH) (hs : s ∈ Icc 0 P.sbar) :
    claimCost P mu s = P.ρ * ((P.T : ℝ) - P.τ - P.w) * (s * P.p *
      (P.K - P.γ * Exi P mu - P.γ * Real.log (Aeff P s - P.c) + P.γ * Real.log (Aeff P s))) := by
  have hdL : P.dL < 0 := hS.2.2.2.2.1
  have hdH : 0 < P.dH := hS.2.2.2.2.2.1
  unfold claimCost
  rw [lost_star P hS hKc _ s (by linarith) hs, lost_star P hS hKc _ s (by linarith) hs]
  unfold Exi xi; ring

lemma Aeff_cont (P : Params) : Continuous (Aeff P) := by
  unfold Aeff; fun_prop

lemma VI_cont (P : Params) (hS : P.Standing) (hKc : KCond P) (mu : ℝ) (hmu : mu ≤ P.muH) :
    ContinuousOn (fun s => EpiI P mu 0 s) (Icc 0 P.sbar) := by
  have hc : 0 < P.c := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h : ContinuousOn (fun s => -0 + QQ P mu - P.ρ * (1 + P.lam) * GG P mu (Aeff P s))
      (Icc 0 P.sbar) := by
    intro s hs
    have hA := Aeff_bounds P hS s hs
    have hG : ContinuousAt (fun s => GG P mu (Aeff P s)) s :=
      ContinuousAt.comp (g := GG P mu) (GG_hasDerivAt P mu _ hc hA.1).continuousAt
        (Aeff_cont P).continuousAt
    exact (continuousAt_const.sub (continuousAt_const.mul hG)).continuousWithinAt
  exact h.congr (fun s hs => EpiI_formula P hS hKc mu 0 s hmu hs)

lemma CC_cont (P : Params) (hS : P.Standing) (hKc : KCond P) (mu : ℝ) (hmu : mu ≤ P.muH) :
    ContinuousOn (fun s => claimCost P mu s) (Icc 0 P.sbar) := by
  have h : ContinuousOn (fun s => P.ρ * ((P.T : ℝ) - P.τ - P.w) * (s * P.p *
      (P.K - P.γ * Exi P mu - P.γ * Real.log (Aeff P s - P.c) + P.γ * Real.log (Aeff P s))))
      (Icc 0 P.sbar) := by
    intro s hs
    have hA := Aeff_bounds P hS s hs
    have h1 : Aeff P s - P.c ≠ 0 := by linarith [hA.1]
    have h2 : Aeff P s ≠ 0 := by linarith [hA.1, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    have hAc : ContinuousAt (Aeff P) s := (Aeff_cont P).continuousAt
    have l1 : ContinuousAt (fun s => Real.log (Aeff P s - P.c)) s :=
      ContinuousAt.comp (g := Real.log) (f := fun s => Aeff P s - P.c)
        (Real.continuousAt_log h1) (hAc.sub continuousAt_const)
    have l2 : ContinuousAt (fun s => Real.log (Aeff P s)) s :=
      ContinuousAt.comp (g := Real.log) (f := Aeff P) (Real.continuousAt_log h2) hAc
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul ((continuousAt_id.mul continuousAt_const).mul
      ((continuousAt_const.sub (continuousAt_const.mul l1)).add (continuousAt_const.mul l2)))
  exact h.congr (fun s hs => claimCost_formula P hS hKc mu s hmu hs)

lemma EpiN_eq (P : Params) (mu : ℝ) : EpiN P mu = EpiI P mu 0 0 := by
  have hA0 : Aeff P 0 = ((P.T : ℝ) - P.τ) * P.p := by unfold Aeff; ring
  have he : ∀ m, eStar P m 0 = eHat P m := by
    intro m; unfold eStar eHat; rw [hA0]
  unfold EpiN EpiI
  rw [he, he]
  unfold piI1e piN1e piI0 piN0 lostSales
  ring

lemma feasible_order (P : Params) (hS : P.Standing) (hKc : KCond P) (M : Menu)
    (hM : Feasible P M) : M.sH ≤ M.sL := by
  obtain ⟨hsH, hsL, h1, h2, h3, h4⟩ := hM
  by_contra h
  replace h := not_le.mp h
  have hD := D_strict P hS hKc M.sL M.sH hsL hsH h
  unfold IC_HL at h1
  unfold IC_LH at h2
  rw [EpiI_y P _ M.yL, EpiI_y P _ M.yH] at h1 h2
  linarith

lemma feasible_bound (P : Params) (hS : P.Standing) (M : Menu) (hM : Feasible P M) :
    insurerProfit P M ≤ R P M.sH M.sL := by
  obtain ⟨hsH, hsL, h1, h2, h3, h4⟩ := hM
  have hα0 : 0 < P.α := hS.2.2.2.2.2.2.2.2.2.1
  have hα1 : P.α < 1 := hS.2.2.2.2.2.2.2.2.2.2.1
  unfold IC_LH at h2
  unfold IR_H at h3
  rw [EpiI_y P _ M.yL, EpiI_y P _ M.yH] at h2
  rw [EpiI_y P _ M.yH] at h3
  have eH : M.yH ≤ gH P M.sH := by unfold gH; linarith
  have eL : M.yL ≤ gL P M.sH M.sL := by unfold gL; linarith
  unfold R insurerProfit
  simp only
  have := mul_le_mul_of_nonneg_left eH hα0.le
  have := mul_le_mul_of_nonneg_left eL (by linarith : (0:ℝ) ≤ 1 - P.α)
  nlinarith

lemma star_feasible (P : Params) (hS : P.Standing) (hKc : KCond P) (a b : ℝ)
    (ha : a ∈ Icc 0 P.sbar) (hb : b ∈ Icc 0 P.sbar) (hab : a ≤ b) :
    Feasible P ⟨gH P a, a, gL P a b, b⟩ := by
  have hsb : (0:ℝ) ∈ Icc 0 P.sbar := ⟨le_rfl, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le⟩
  have hD := D_anti P hS hKc a b ha hb hab
  have hD0 := D_anti P hS hKc 0 a hsb ha ha.1
  refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
  · unfold IC_HL; simp only
    rw [EpiI_y P _ (gL P a b), EpiI_y P _ (gH P a)]
    unfold gL; linarith
  · unfold IC_LH; simp only
    rw [EpiI_y P _ (gL P a b), EpiI_y P _ (gH P a)]
    unfold gL; linarith
  · unfold IR_H; simp only
    rw [EpiI_y P _ (gH P a)]
    unfold gH; linarith
  · unfold IR_L; simp only
    rw [EpiI_y P _ (gL P a b), EpiN_eq P P.muL]
    have := EpiN_eq P P.muH
    unfold gL gH; linarith

theorem main (P : Params) (hS : P.Standing) (hK : KCond P) (_h55 : Cond55 P) :
    (∃ M : Menu, IsOptimalMenu P M) ∧
      ∀ M : Menu, IsOptimalMenu P M → M.sH ≤ M.sL ∧ M.yH ≤ M.yL := by
  have hmu : P.muL ≤ P.muH := hS.2.2.2.1.le
  set u : ℝ → ℝ := fun a => P.α * (gH P a - claimCost P P.muH a)
    + (1 - P.α) * (gH P a - EpiI P P.muL 0 a) with hu
  set v : ℝ → ℝ := fun b => (1 - P.α) * (EpiI P P.muL 0 b - claimCost P P.muL b) with hv
  have hR : ∀ a b, R P a b = u a + v b := by
    intro a b; simp only [hu, hv]; unfold R insurerProfit gL; ring
  have huc : ContinuousOn u (Icc 0 P.sbar) := by
    have hgH : ContinuousOn (gH P) (Icc 0 P.sbar) := by
      unfold gH; exact (VI_cont P hS hK P.muH le_rfl).sub continuousOn_const
    exact (continuousOn_const.mul (hgH.sub (CC_cont P hS hK P.muH le_rfl))).add
      (continuousOn_const.mul (hgH.sub (VI_cont P hS hK P.muL hmu)))
  have hvc : ContinuousOn v (Icc 0 P.sbar) :=
    continuousOn_const.mul ((VI_cont P hS hK P.muL hmu).sub (CC_cont P hS hK P.muL hmu))
  set S : Set (ℝ × ℝ) := (Icc 0 P.sbar ×ˢ Icc 0 P.sbar) ∩ {q | q.1 ≤ q.2} with hSdef
  have hScpt : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_fst continuous_snd)
  have hsb : (0:ℝ) ∈ Icc 0 P.sbar := ⟨le_rfl, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le⟩
  have hSne : S.Nonempty := ⟨(0, 0), ⟨⟨hsb, hsb⟩, le_refl (0:ℝ)⟩⟩
  have hφc : ContinuousOn (fun q : ℝ × ℝ => u q.1 + v q.2) S := by
    apply ContinuousOn.add
    · exact huc.comp continuousOn_fst (fun q hq => hq.1.1)
    · exact hvc.comp continuousOn_snd (fun q hq => hq.1.2)
  obtain ⟨q, hqS, hqmax⟩ := hScpt.exists_isMaxOn hSne hφc
  refine ⟨⟨⟨gH P q.1, q.1, gL P q.1 q.2, q.2⟩,
    star_feasible P hS hK q.1 q.2 hqS.1.1 hqS.1.2 hqS.2, ?_⟩, ?_⟩
  · intro M' hM'
    have h1 := feasible_bound P hS M' hM'
    have hord := feasible_order P hS hK M' hM'
    have hmem : (M'.sH, M'.sL) ∈ S := ⟨⟨hM'.1, hM'.2.1⟩, hord⟩
    have h2 := isMaxOn_iff.mp hqmax _ hmem
    have h3 : insurerProfit P ⟨gH P q.1, q.1, gL P q.1 q.2, q.2⟩ = R P q.1 q.2 := rfl
    rw [h3, hR]
    rw [hR] at h1
    exact h1.trans h2
  · intro M hM
    have hF := hM.1
    have hord := feasible_order P hS hK M hF
    refine ⟨hord, ?_⟩
    obtain ⟨hsH, hsL, h1, h2, h3, h4⟩ := hF
    have hV := VH_mono P hS hK M.sH M.sL hsH hsL hord
    unfold IC_HL at h1
    rw [EpiI_y P _ M.yL, EpiI_y P _ M.yH] at h1
    linarith

end BIInsurance.Screening.P4

open BIInsurance.Screening in
theorem solution (P : Params) (hS : P.Standing) (hK : KCond P) (h55 : Cond55 P) :
    (∃ M : Menu, IsOptimalMenu P M) ∧
      ∀ M : Menu, IsOptimalMenu P M → M.sH ≤ M.sL ∧ M.yH ≤ M.yL :=
  BIInsurance.Screening.P4.main P hS hK h55
