-- Prove2me | solution 1 for BrandLicensing.Intensive.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T17:16:12.962581+00:00
-- url     : https://prove2.me/submissions/8d9ad0c1-5da9-4f8c-a701-3a91c06bfe75

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

set_option autoImplicit false

open BrandLicensing.Intensive in
/-- The licensee's best response is unique and equals the closed form (12). -/
theorem bl_licensee_resp (P : Params) (hP : P.Standing) (c s e : ℝ) (he : 0 ≤ e)
    (hopt : ∀ e', 0 ≤ e' → piLicensee P c s e' ≤ piLicensee P c s e) :
    e = eE12 P c s := by
  obtain ⟨hα0, hα1, hθ, hμ, hρ0, hρ1, hl0, hl1, hε⟩ := hP
  have h2 : 0 < 2 - P.ρ := by linarith
  unfold piLicensee piM at hopt
  unfold eE12
  by_cases hk : 0 ≤ (1 - P.α) * c - s
  · rw [max_eq_left hk]
    obtain ⟨e0, he0⟩ : ∃ e0, e0 = P.ρ / (2 - P.ρ) * ((1 - P.α) * c - s) := ⟨_, rfl⟩
    rw [← he0]
    have he0nn : 0 ≤ e0 := he0 ▸ mul_nonneg (div_nonneg hρ0 h2.le) hk
    have hfoc : (2 - P.ρ) * e0 = P.ρ * ((1 - P.α) * c - s) := by
      rw [he0]; field_simp
    have h := hopt e0 he0nn
    rw [max_eq_left (by linarith), max_eq_left (by linarith)] at h
    have hid : (2 - P.ρ) * (e - e0) ^ 2 = 4 * ((P.ρ * (e0 + (1 - P.α) * c - s) ^ 2 / 4 - e0 ^ 2 / 2)
        - (P.ρ * (e + (1 - P.α) * c - s) ^ 2 / 4 - e ^ 2 / 2)) := by
      linear_combination (-2 * (e - e0)) * hfoc
    have hq : (2 - P.ρ) * (e - e0) ^ 2 ≤ 0 := by rw [hid]; linarith
    have hX : (e - e0) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos h2 hc]
    have := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hX (sq_nonneg _))
    linarith
  · push_neg at hk
    rw [max_eq_right hk.le, mul_zero]
    have h := hopt 0 le_rfl
    rw [max_eq_right (by linarith : 0 + (1 - P.α) * c - s ≤ 0)] at h
    have hm0 : 0 ≤ max (e + (1 - P.α) * c - s) 0 := le_max_right _ _
    have hme : max (e + (1 - P.α) * c - s) 0 ≤ e := max_le (by linarith) he
    have hm2 : (max (e + (1 - P.α) * c - s) 0) ^ 2 ≤ e ^ 2 := by nlinarith
    have he2 : e ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hm2), mul_nonneg (sub_nonneg.2 hρ1.le) (sq_nonneg e)]
    exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm he2 (sq_nonneg e))

open BrandLicensing.Intensive in
theorem bl_W_in (P : Params) (hP : P.Standing) (c s : ℝ) (hs : s ≤ (1 - P.α) * c) :
    piOwnerLic P c s (eE12 P c s) =
      P.μ * (c + P.lam * (1 - P.α) * (P.ρ / (2 - P.ρ) * ((1 - P.α) * c - s) - P.ε))
        + s * P.ρ * ((1 - P.α) * c - s) / (2 - P.ρ) - c ^ 2 / 2 := by
  obtain ⟨hα0, hα1, hθ, hμ, hρ0, hρ1, hl0, hl1, hε⟩ := hP
  have h2 : 0 < 2 - P.ρ := by linarith
  have hk : 0 ≤ (1 - P.α) * c - s := by linarith
  have hk2 := mul_nonneg (div_nonneg hρ0 h2.le) hk
  unfold piOwnerLic vC eE12
  rw [max_eq_left hk, max_eq_left (by linarith)]
  field_simp
  ring

open BrandLicensing.Intensive in
theorem bl_W_out (P : Params) (c s : ℝ) (hs : (1 - P.α) * c < s) :
    piOwnerLic P c s (eE12 P c s) = P.μ * (c - P.lam * (1 - P.α) * P.ε) - c ^ 2 / 2 := by
  unfold piOwnerLic vC eE12
  rw [max_eq_right (by linarith : (1 - P.α) * c - s ≤ 0), mul_zero, add_zero,
    max_eq_right (by linarith : (1 - P.α) * c - s ≤ 0)]
  ring

open BrandLicensing.Intensive in
theorem bl_Q (P : Params) (hP : P.Standing) (c e : ℝ) (hc : 0 ≤ c) (he : 0 ≤ e) :
    piInHouse P c e = P.μ * (c + P.lam * (1 - P.α) * (e - P.ε))
      + P.ρ * (e + (1 - P.α) * c) ^ 2 / 4 - P.θ * e ^ 2 / 2 - c ^ 2 / 2 := by
  obtain ⟨hα0, hα1, hθ, hμ, hρ0, hρ1, hl0, hl1, hε⟩ := hP
  have : 0 ≤ (1 - P.α) * c := mul_nonneg (by linarith) hc
  unfold piInHouse vC piM
  rw [sub_zero, max_eq_left (by linarith)]

theorem bl_G1 (a ρ μ l ε c s cs ss D : ℝ) (h2 : 2 - ρ ≠ 0) (hDdef : D = 4 - (2 + a ^ 2) * ρ)
    (hD : D ≠ 0)
    (hcs : cs = μ * (4 - 2 * ρ + l * a ^ 2 * ρ) / D)
    (hss : ss = a * (cs - l * μ) / 2) :
    μ * (c + l * a * (ρ / (2 - ρ) * (a * c - s) - ε)) + s * ρ * (a * c - s) / (2 - ρ) - c ^ 2 / 2
      = (μ ^ 2 * (4 + a ^ 2 * l * (2 + l) * ρ - 2 * ρ) / (2 * D) - a * l * ε * μ)
        - ((2 - ρ) * (c - cs) ^ 2 - 2 * ρ * a * (c - cs) * (s - ss) + 2 * ρ * (s - ss) ^ 2)
          / (2 * (2 - ρ)) := by
  subst hss hcs
  field_simp
  subst hDdef
  ring

theorem bl_G2 (a ρ μ l ε θ c e cH eH X : ℝ) (hXdef : X = θ * (2 - a ^ 2 * ρ) - ρ) (hX : X ≠ 0)
    (hcH : cH = μ * (2 * θ - ρ * (1 - a ^ 2 * l)) / X)
    (heH : eH = a * μ * (l * (2 - a ^ 2 * ρ) + ρ) / X) :
    μ * (c + l * a * (e - ε)) + ρ * (e + a * c) ^ 2 / 4 - θ * e ^ 2 / 2 - c ^ 2 / 2
      = (μ ^ 2 * (2 * θ + 2 * a ^ 2 * l ^ 2 - ρ * (1 - a ^ 2 * l) ^ 2)
            / (2 * X) - a * l * ε * μ)
        - ((2 - ρ * a ^ 2) * (c - cH) ^ 2 - 2 * ρ * a * (c - cH) * (e - eH)
            + (2 * θ - ρ) * (e - eH) ^ 2) / 4 := by
  subst hcH heH
  field_simp
  subst hXdef
  ring

theorem bl_G3 (a ρ μ l ε D : ℝ) (hDdef : D = 4 - (2 + a ^ 2) * ρ) (hD : D ≠ 0) :
    (μ ^ 2 * (4 + a ^ 2 * l * (2 + l) * ρ - 2 * ρ) / (2 * D) - a * l * ε * μ)
      = (μ ^ 2 / 2 - a * l * ε * μ) + μ ^ 2 * ρ * a ^ 2 * (1 + l) ^ 2 / (2 * D) := by
  field_simp
  subst hDdef
  ring

theorem bl_G4 (a ρ μ l cs ss D : ℝ) (h2 : 2 - ρ ≠ 0) (hDdef : D = 4 - (2 + a ^ 2) * ρ)
    (hD : D ≠ 0)
    (hcs : cs = μ * (4 - 2 * ρ + l * a ^ 2 * ρ) / D)
    (hss : ss = a * (cs - l * μ) / 2) :
    ρ / (2 - ρ) * (a * cs - ss) * D = a * μ * ρ * (1 + l) := by
  subst hss hcs
  field_simp
  subst hDdef
  ring

theorem bl_G5 (a ρ l θ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hθ : 1 ≤ θ)
    (key : (2 * θ + (2 * a ^ 2 * l ^ 2 - ρ * (1 - a ^ 2 * l) ^ 2)) * (4 - (2 + a ^ 2) * ρ)
      = (4 + a ^ 2 * l * (2 + l) * ρ - 2 * ρ) * (θ * (2 - a ^ 2 * ρ) - ρ)) :
    (l * (2 - a ^ 2 * ρ) + ρ) * (4 - (2 + a ^ 2) * ρ) < ρ * (1 + l) * (θ * (2 - a ^ 2 * ρ) - ρ) := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hb : 0 < 2 - a ^ 2 * ρ := by nlinarith
  have hx : 0 < θ * (2 - a ^ 2 * ρ) - ρ := by nlinarith [mul_le_mul_of_nonneg_right hθ hb.le]
  have hy : 0 < l * (2 - a ^ 2 * ρ) + ρ := by nlinarith [mul_nonneg hl0 hb.le]
  have hE : (1 + l) * (2 - a ^ 2 * ρ - ρ) - (4 - (2 + a ^ 2) * ρ) ≤ - (a ^ 2 * ρ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hl1) (by nlinarith : (0:ℝ) ≤ 2 - a ^ 2 * ρ - ρ)]
  have ha2p : 0 < a ^ 2 := by positivity
  have k1 : a ^ 2 * ((θ * (2 - a ^ 2 * ρ) - ρ) * (ρ * ((1 + l) * (l * (2 - a ^ 2 * ρ) + ρ)
      + ((1 + l) * (2 - a ^ 2 * ρ - ρ) - (4 - (2 + a ^ 2) * ρ)))))
      = a ^ 2 * ((l * (2 - a ^ 2 * ρ) + ρ) ^ 2 * (4 - (2 + a ^ 2) * ρ)) := by
    linear_combination (-(2 - a ^ 2 * ρ)) * key
  have k2 := mul_left_cancel₀ ha2p.ne' k1
  have hxE : (θ * (2 - a ^ 2 * ρ) - ρ) * ρ
      * ((1 + l) * (2 - a ^ 2 * ρ - ρ) - (4 - (2 + a ^ 2) * ρ)) < 0 := by
    have : 0 < (θ * (2 - a ^ 2 * ρ) - ρ) * ρ := mul_pos hx hρ
    nlinarith [mul_pos this (mul_pos ha2p hρ)]
  have k3 : (l * (2 - a ^ 2 * ρ) + ρ) * ((l * (2 - a ^ 2 * ρ) + ρ) * (4 - (2 + a ^ 2) * ρ))
      < (l * (2 - a ^ 2 * ρ) + ρ) * (ρ * (1 + l) * (θ * (2 - a ^ 2 * ρ) - ρ)) := by
    nlinarith [k2, hxE]
  exact lt_of_mul_lt_mul_left k3 hy.le

set_option maxHeartbeats 1000000 in
open BrandLicensing.Intensive in
theorem solution (P : Params) (hP : P.Standing)
    (eCH eEH : ℝ) (hH : IsInHouseEq P eCH eEH)
    (σ : LicProfile) (hL : IsLicensingSPE P σ)
    (hI : piInHouse P eCH eEH = piOwnerLic P σ.eC σ.sL σ.eEL)
    (hNE : ∀ c, 0 ≤ c → piNoExt P c < piInHouse P eCH eEH) :
    eEH < σ.eEL ∧
    ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν],
      ν {ξ | σ.eEL + ξ < P.ε} ≤ ν {ξ | eEH + ξ < P.ε} ∧
      ((∀ x y : ℝ, x < y → 0 < ν (Set.Ioo x y)) →
        ν {ξ | σ.eEL + ξ < P.ε} < ν {ξ | eEH + ξ < P.ε}) := by
  obtain ⟨hα0, hα1, hθ, hμ, hρ0, hρ1, hl0, hl1, hε⟩ := id hP
  have ha0 : 0 ≤ 1 - P.α := by linarith
  have ha1 : 1 - P.α ≤ 1 := by linarith
  have ha2 : (1 - P.α) ^ 2 ≤ 1 := by nlinarith
  have h2 : 0 < 2 - P.ρ := by linarith
  have hD : 0 < 4 - (2 + (1 - P.α) ^ 2) * P.ρ := by nlinarith [mul_le_mul_of_nonneg_left ha2 hρ0]
  have hb : 0 < 2 - (1 - P.α) ^ 2 * P.ρ := by nlinarith [mul_le_mul_of_nonneg_left ha2 hρ0]
  have hX : 0 < P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ := by
    nlinarith [mul_le_mul_of_nonneg_right hθ hb.le]
  -- licensee best response
  have hσE : ∀ c, 0 ≤ c → ∀ s, 0 ≤ s → σ.σE c s = eE12 P c s := fun c hc s hs =>
    bl_licensee_resp P hP c s (σ.σE c s) (hL.1 c hc s hs).1 (hL.1 c hc s hs).2
  -- the licensing optimum
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = P.μ * (4 - 2 * P.ρ + P.lam * (1 - P.α) ^ 2 * P.ρ)
      / (4 - (2 + (1 - P.α) ^ 2) * P.ρ) := ⟨_, rfl⟩
  obtain ⟨ss, hss⟩ : ∃ ss, ss = (1 - P.α) * (cs - P.lam * P.μ) / 2 := ⟨_, rfl⟩
  obtain ⟨Ls, hLs⟩ : ∃ Ls, Ls = P.μ ^ 2 * (4 + (1 - P.α) ^ 2 * P.lam * (2 + P.lam) * P.ρ - 2 * P.ρ)
      / (2 * (4 - (2 + (1 - P.α) ^ 2) * P.ρ)) - (1 - P.α) * P.lam * P.ε * P.μ := ⟨_, rfl⟩
  have hG3 := bl_G3 (1 - P.α) P.ρ P.μ P.lam P.ε _ rfl hD.ne'
  rw [← hLs] at hG3
  have hgap : 0 ≤ P.μ ^ 2 * P.ρ * (1 - P.α) ^ 2 * (1 + P.lam) ^ 2
      / (2 * (4 - (2 + (1 - P.α) ^ 2) * P.ρ)) :=
    div_nonneg (by positivity) (by linarith)
  have hlε : 0 ≤ (1 - P.α) * P.lam * P.ε * P.μ :=
    mul_nonneg (mul_nonneg (mul_nonneg ha0 hl0) hε.le) hμ.le
  have hcs_ge : P.μ ≤ cs := by
    rw [hcs, le_div_iff₀ hD]
    linarith [mul_nonneg hμ.le (add_nonneg (mul_nonneg (mul_nonneg hl0 (sq_nonneg (1 - P.α))) hρ0) (mul_nonneg (sq_nonneg (1 - P.α)) hρ0)), mul_nonneg (mul_nonneg hl0 (sq_nonneg (1 - P.α))) hρ0,
      mul_nonneg (sq_nonneg (1 - P.α)) hρ0]
  have hcs0 : 0 ≤ cs := by linarith
  have hss0 : 0 ≤ ss := by
    rw [hss]; apply div_nonneg _ (by norm_num)
    apply mul_nonneg ha0; linarith [mul_le_mul_of_nonneg_right hl1 hμ.le]
  have hssin : ss ≤ (1 - P.α) * cs := by
    rw [hss]; linarith [mul_nonneg ha0 hcs0, mul_nonneg ha0 (mul_nonneg hl0 hμ.le)]
  have hWq := fun c s => bl_G1 (1 - P.α) P.ρ P.μ P.lam P.ε c s cs ss _ h2.ne' rfl hD.ne' hcs hss
  have hqL : ∀ d1 d2 : ℝ, 0 ≤ (2 - P.ρ) * d1 ^ 2 - 2 * P.ρ * (1 - P.α) * d1 * d2 + 2 * P.ρ * d2 ^ 2 := by
    intro d1 d2
    linarith [mul_nonneg hρ0 (sq_nonneg (2 * d2 - (1 - P.α) * d1)), mul_nonneg hD.le (sq_nonneg d1)]
  have hWle : ∀ c, 0 ≤ c → ∀ s, 0 ≤ s → piOwnerLic P c s (eE12 P c s) ≤ Ls := by
    intro c hc s hs
    by_cases hin : s ≤ (1 - P.α) * c
    · rw [bl_W_in P hP c s hin, hWq c s, ← hLs]
      have := div_nonneg (hqL (c - cs) (s - ss)) (by linarith : (0:ℝ) ≤ 2 * (2 - P.ρ))
      linarith
    · push_neg at hin
      rw [bl_W_out P c s hin]
      linarith [sq_nonneg (c - P.μ), hG3, hgap, hlε]
  have hc0 : 0 ≤ σ.eC := hL.2.2.1
  have hs0 : 0 ≤ σ.σs σ.eC := (hL.2.1 σ.eC hc0).1
  have heEL : σ.eEL = eE12 P σ.eC σ.sL := hσE _ hc0 _ hs0
  have hπL : piOwnerLic P σ.eC σ.sL σ.eEL = Ls := by
    apply le_antisymm
    · rw [heEL]; exact hWle _ hc0 _ hs0
    · have e1 : piOwnerLic P cs ss (eE12 P cs ss) = Ls := by
        rw [bl_W_in P hP cs ss hssin, hWq cs ss, ← hLs]; simp
      have e2 := (hL.2.1 cs hcs0).2 ss hss0
      rw [hσE cs hcs0 ss hss0, e1] at e2
      exact e2.trans (hL.2.2.2 cs hcs0)
  -- the no-extension bound
  have hNEμ := hNE P.μ hμ.le
  unfold piNoExt at hNEμ
  rw [hI, hπL] at hNEμ
  have hpos : 0 < P.ρ * (1 - P.α) ^ 2 := by
    by_contra hc
    push_neg at hc
    have h0 : P.ρ * (1 - P.α) ^ 2 = 0 := le_antisymm hc (by positivity)
    have : P.μ ^ 2 * P.ρ * (1 - P.α) ^ 2 * (1 + P.lam) ^ 2
        / (2 * (4 - (2 + (1 - P.α) ^ 2) * P.ρ)) = 0 := by
      rw [mul_assoc (P.μ ^ 2), h0]; simp
    linarith
  have hρp : 0 < P.ρ := by
    rcases hρ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  have hap : 0 < 1 - P.α := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  -- the on-path royalty is below the cut-off, then the optimum is unique
  have hin : σ.sL ≤ (1 - P.α) * σ.eC := by
    by_contra hc
    push_neg at hc
    have := hπL
    rw [heEL, bl_W_out P _ _ hc] at this
    linarith [sq_nonneg (σ.eC - P.μ), hG3, hgap, hlε]
  have hq0 := hπL
  rw [heEL, bl_W_in P hP _ _ hin, hWq, ← hLs] at hq0
  have hq : (2 - P.ρ) * (σ.eC - cs) ^ 2 - 2 * P.ρ * (1 - P.α) * (σ.eC - cs) * (σ.sL - ss)
      + 2 * P.ρ * (σ.sL - ss) ^ 2 = 0 := by
    have h' : ((2 - P.ρ) * (σ.eC - cs) ^ 2 - 2 * P.ρ * (1 - P.α) * (σ.eC - cs) * (σ.sL - ss)
      + 2 * P.ρ * (σ.sL - ss) ^ 2) / (2 * (2 - P.ρ)) = 0 := by linarith
    rcases div_eq_zero_iff.mp h' with h | h
    · exact h
    · exfalso; linarith
  have hDd : (4 - (2 + (1 - P.α) ^ 2) * P.ρ) * (σ.eC - cs) ^ 2 ≤ 0 := by
    linarith [mul_nonneg hρ0 (sq_nonneg (2 * (σ.sL - ss) - (1 - P.α) * (σ.eC - cs)))]
  have hd1 : σ.eC = cs := by
    have h' : (σ.eC - cs) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      linarith [mul_pos hD hc]
    have := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h' (sq_nonneg _))
    linarith
  have hd2 : σ.sL = ss := by
    rw [hd1, sub_self] at hq
    have h' : P.ρ * (σ.sL - ss) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp h' with h | h
    · linarith
    · have := (pow_eq_zero_iff two_ne_zero).mp h
      linarith
  have heELD : σ.eEL * (4 - (2 + (1 - P.α) ^ 2) * P.ρ)
      = (1 - P.α) * P.μ * P.ρ * (1 + P.lam) := by
    rw [heEL, hd1, hd2]
    unfold eE12
    rw [max_eq_left (sub_nonneg.2 hssin)]
    exact bl_G4 (1 - P.α) P.ρ P.μ P.lam cs ss _ h2.ne' rfl hD.ne' hcs hss
  -- the in-house optimum
  obtain ⟨cH, hcH⟩ : ∃ cH, cH = P.μ * (2 * P.θ - P.ρ * (1 - (1 - P.α) ^ 2 * P.lam))
      / (P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ) := ⟨_, rfl⟩
  obtain ⟨eH, heH⟩ : ∃ eH, eH = (1 - P.α) * P.μ * (P.lam * (2 - (1 - P.α) ^ 2 * P.ρ) + P.ρ)
      / (P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ) := ⟨_, rfl⟩
  obtain ⟨Hs, hHs⟩ : ∃ Hs, Hs = P.μ ^ 2 * (2 * P.θ + 2 * (1 - P.α) ^ 2 * P.lam ^ 2
      - P.ρ * (1 - (1 - P.α) ^ 2 * P.lam) ^ 2) / (2 * (P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ))
      - (1 - P.α) * P.lam * P.ε * P.μ := ⟨_, rfl⟩
  have hcH0 : 0 ≤ cH := by
    rw [hcH]; apply div_nonneg _ hX.le
    apply mul_nonneg hμ.le
    linarith [mul_nonneg hρ0 (mul_nonneg (sq_nonneg (1 - P.α)) hl0)]
  have heH0 : 0 ≤ eH := by
    rw [heH]; apply div_nonneg _ hX.le
    apply mul_nonneg (mul_nonneg ha0 hμ.le)
    linarith [mul_nonneg hl0 hb.le]
  have hQ := fun c e => bl_G2 (1 - P.α) P.ρ P.μ P.lam P.ε P.θ c e cH eH _ rfl hX.ne' hcH heH
  have hHopt := hH.2.2 cH hcH0 eH heH0
  have hπH := bl_Q P hP eCH eEH hH.1 hH.2.1
  rw [bl_Q P hP cH eH hcH0 heH0, hπH, hQ, hQ, ← hHs] at hHopt
  rw [hQ, ← hHs] at hπH
  have hqH : ∀ d1 d2 : ℝ, P.ρ * ((1 - P.α) * d1 - d2) ^ 2 + (2 - 2 * P.ρ * (1 - P.α) ^ 2) * d1 ^ 2
      + (2 * P.θ - 2 * P.ρ) * d2 ^ 2
      = (2 - P.ρ * (1 - P.α) ^ 2) * d1 ^ 2 - 2 * P.ρ * (1 - P.α) * d1 * d2
        + (2 * P.θ - P.ρ) * d2 ^ 2 := by intro d1 d2; ring
  have hc1 : 0 ≤ 2 - 2 * P.ρ * (1 - P.α) ^ 2 := by linarith [mul_le_mul_of_nonneg_left ha2 hρ0]
  have hc2 : 0 < 2 * P.θ - 2 * P.ρ := by linarith
  have hqpos := hqH (eCH - cH) (eEH - eH)
  have hqge : 0 ≤ (2 - P.ρ * (1 - P.α) ^ 2) * (eCH - cH) ^ 2
      - 2 * P.ρ * (1 - P.α) * (eCH - cH) * (eEH - eH) + (2 * P.θ - P.ρ) * (eEH - eH) ^ 2 := by
    rw [← hqpos]
    have := mul_nonneg hρ0 (sq_nonneg ((1 - P.α) * (eCH - cH) - (eEH - eH)))
    have := mul_nonneg hc1 (sq_nonneg (eCH - cH))
    have := mul_nonneg hc2.le (sq_nonneg (eEH - eH))
    linarith
  have hπHv : piInHouse P eCH eEH = Hs := by
    rw [hπH]; simp only [sub_self] at hHopt; linarith
  have hdH : eEH = eH := by
    simp only [sub_self] at hHopt
    have h' : (2 * P.θ - 2 * P.ρ) * (eEH - eH) ^ 2 ≤ 0 := by
      have := mul_nonneg hρ0 (sq_nonneg ((1 - P.α) * (eCH - cH) - (eEH - eH)))
      have := mul_nonneg hc1 (sq_nonneg (eCH - cH))
      linarith
    have h'' : (eEH - eH) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      linarith [mul_pos hc2 hc]
    have := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h'' (sq_nonneg _))
    linarith
  -- indifference
  have hHL : Hs = Ls := by rw [← hπHv, hI, hπL]
  have e0 : P.μ ^ 2 * (2 * P.θ + 2 * (1 - P.α) ^ 2 * P.lam ^ 2
      - P.ρ * (1 - (1 - P.α) ^ 2 * P.lam) ^ 2) / (2 * (P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ))
      = P.μ ^ 2 * (4 + (1 - P.α) ^ 2 * P.lam * (2 + P.lam) * P.ρ - 2 * P.ρ)
      / (2 * (4 - (2 + (1 - P.α) ^ 2) * P.ρ)) := by
    rw [hHs, hLs] at hHL; linarith
  rw [div_eq_div_iff (mul_pos two_pos hX).ne' (mul_pos two_pos hD).ne'] at e0
  have key : (2 * P.θ + (2 * (1 - P.α) ^ 2 * P.lam ^ 2 - P.ρ * (1 - (1 - P.α) ^ 2 * P.lam) ^ 2))
      * (4 - (2 + (1 - P.α) ^ 2) * P.ρ)
      = (4 + (1 - P.α) ^ 2 * P.lam * (2 + P.lam) * P.ρ - 2 * P.ρ)
        * (P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ) := by
    have hμ2 : (2 * P.μ ^ 2) ≠ 0 := by positivity
    apply mul_left_cancel₀ hμ2
    linear_combination e0
  have g5 := bl_G5 (1 - P.α) P.ρ P.lam P.θ hap ha1 hρp hρ1 hl0 hl1 hθ key
  have hlt : eEH < σ.eEL := by
    have hEL : σ.eEL = (1 - P.α) * P.μ * P.ρ * (1 + P.lam) / (4 - (2 + (1 - P.α) ^ 2) * P.ρ) := by
      rw [eq_div_iff hD.ne']; exact heELD
    rw [hdH, heH, hEL, div_lt_div_iff₀ hX hD]
    linarith [mul_lt_mul_of_pos_left g5 (mul_pos hap hμ)]
  refine ⟨hlt, fun ν _ => ?_⟩
  have hsub : {ξ : ℝ | σ.eEL + ξ < P.ε} ⊆ {ξ | eEH + ξ < P.ε} := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    linarith
  refine ⟨MeasureTheory.measure_mono hsub, fun hfull => ?_⟩
  have hIoo : Set.Ioo (P.ε - σ.eEL) (P.ε - eEH)
      ⊆ {ξ : ℝ | eEH + ξ < P.ε} \ {ξ | σ.eEL + ξ < P.ε} := by
    intro ξ hξ
    simp only [Set.mem_Ioo] at hξ
    simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt]
    constructor <;> linarith [hξ.1, hξ.2]
  have hmeas : MeasurableSet {ξ : ℝ | σ.eEL + ξ < P.ε} :=
    measurableSet_lt (measurable_const.add measurable_id) measurable_const
  have h3 := lt_of_lt_of_le (hfull _ _ (by linarith : P.ε - σ.eEL < P.ε - eEH))
    (MeasureTheory.measure_mono hIoo)
  rw [MeasureTheory.measure_sdiff hsub hmeas.nullMeasurableSet
    (MeasureTheory.measure_ne_top _ _)] at h3
  exact tsub_pos_iff_lt.mp h3
