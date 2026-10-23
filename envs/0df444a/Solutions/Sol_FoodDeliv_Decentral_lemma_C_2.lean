-- Prove2me | solution 1 for FoodDeliv.Decentral.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:58:32.81255+00:00
-- url     : https://prove2.me/submissions/8b210c56-ffec-41dd-879e-167d20af26c6

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open Set FoodDeliv.Decentral

set_option maxHeartbeats 1000000 in
theorem solution (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (p θ : ℝ) (s : Profile)
    (hs : IsCustEq P p θ s) :
    (p ≤ P.R - P.c / (P.μ - P.Λ1) →
      (0 < θ ∧ θ ≤ (P.c - P.ϕ) * (P.R - p) / P.c →
        s.lamD = P.Λ1 ∧ s.lamW = P.μ - P.c / (P.R - p) - P.Λ1) ∧
      ((P.c - P.ϕ) * (P.R - p) / P.c < θ ∧ θ ≤ P.R - p - P.ϕ / P.μ →
        s.lamD = 0 ∧ s.lamW = P.μ - P.c / (P.R - p))) ∧
    (P.R - P.c / (P.μ - P.Λ1) < p ∧ p ≤ P.R - P.ϕ / P.μ →
      (0 < θ ∧ θ ≤ max (P.R - p - P.ϕ / (P.μ - P.Λ1)) 0 →
        s.lamD = P.Λ1 ∧ s.lamW = 0) ∧
      (max (P.R - p - P.ϕ / (P.μ - P.Λ1)) 0 < θ ∧
          θ ≤ min ((P.c - P.ϕ) * (P.R - p) / P.c) (P.R - p - P.ϕ / P.μ) →
        s.lamD = P.μ - P.ϕ / (P.R - p - θ) ∧ s.lamW = 0) ∧
      (min ((P.c - P.ϕ) * (P.R - p) / P.c) (P.R - p - P.ϕ / P.μ) < θ →
        p ≤ P.R - P.c / P.μ →
        s.lamD = 0 ∧ s.lamW = P.μ - P.c / (P.R - p))) := by
  obtain ⟨R, μ, c, ϕ, Λ0, Λ1⟩ := P
  obtain ⟨hμ, hc, hcR, -, hϕc, hΛ0, hΛ1, hΛ1μ⟩ := hP
  simp only at hμ hc hcR hϕc hΛ0 hΛ1 hΛ1μ hϕ ⊢
  obtain ⟨hD0, h1W0, h0W0, htech, htrad, htot, tjoin, tbalk, tdeliv, twalk, tbal⟩ := hs
  simp only [UW, UD] at tjoin tbalk tdeliv twalk tbal
  simp only [Profile.total, Profile.lamW] at htot tjoin tbalk tdeliv twalk tbal ⊢
  set L := s.lamD + (s.lam0W + s.lam1W) with hL
  have he : 0 < μ - L := by linarith
  set e := μ - L with he_def
  -- general facts
  have G1 : R - p - c / e ≤ 0 := by
    by_contra h; push_neg at h
    have : ¬ s.lam0W < Λ0 := fun hlt => by linarith [tbalk hlt]
    push_neg at this
    linarith
  have G2 : R - p - c / e < 0 → s.lam0W = 0 ∧ s.lam1W = 0 := by
    intro h
    constructor
    · by_contra h'
      have := tjoin (lt_of_le_of_ne h0W0 (Ne.symm h')); linarith
    · by_contra h'
      have := (twalk (lt_of_le_of_ne h1W0 (Ne.symm h'))).1; linarith
  have hΛe : 0 < μ - Λ1 := by linarith
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · -- region 1
    have hRp : c / (μ - Λ1) ≤ R - p := by linarith
    have hRp0 : 0 < R - p := lt_of_lt_of_le (div_pos hc hΛe) hRp
    have hstar : Λ1 ≤ μ - c / (R - p) := by
      have : c / (R - p) ≤ μ - Λ1 := by
        rw [div_le_iff₀ hRp0]; rw [div_le_iff₀ hΛe] at hRp; linarith
      linarith
    -- W = 0
    have hW : R - p - c / e = 0 := by
      rcases G1.lt_or_eq with h | h
      · obtain ⟨h0, h1⟩ := G2 h
        exfalso
        have hLD : L = s.lamD := by rw [hL, h0, h1]; ring
        have : R - p < c / e := by linarith
        rw [lt_div_iff₀ he] at this
        have h2 : (R - p) * e < c := by linarith
        have h3 : c / (R - p) > e := by rw [gt_iff_lt, lt_div_iff₀ hRp0]; linarith
        have : L > Λ1 := by linarith
        linarith
      · exact h
    have hce : c / e = R - p := by linarith
    have he_eq : e = c / (R - p) := by
      field_simp at hce ⊢; linarith
    have hDW : (R - p - θ - ϕ / e) - (R - p - c / e) = (c - ϕ) * (R - p) / c - θ := by
      rw [he_eq]; field_simp; ring
    refine ⟨fun hθ => ?_, fun hθ => ?_⟩
    · have hD : 0 ≤ R - p - θ - ϕ / e := by
        have : 0 ≤ (c - ϕ) * (R - p) / c - θ := by linarith [hθ.2]
        linarith
      have h1 : s.lam1W = 0 := by
        by_contra h'
        have := (twalk (lt_of_le_of_ne h1W0 (Ne.symm h'))).2; linarith
      have hD1 : s.lamD = Λ1 := by
        by_contra h'
        have hlt : s.lamD + s.lam1W < Λ1 := by
          rw [h1, add_zero]; exact lt_of_le_of_ne (by linarith) h'
        obtain ⟨hDle, -, htie⟩ := tbal hlt
        have h0 := htie ⟨by linarith, by linarith⟩
        have : L = s.lamD := by rw [hL, h0, h1]; ring
        have : L = μ - c / (R - p) := by linarith
        linarith
      refine ⟨hD1, ?_⟩
      have : s.lam0W + s.lam1W = L - s.lamD := by rw [hL]; ring
      rw [this, hD1]; linarith
    · have hD : R - p - θ - ϕ / e < 0 := by
        have : (c - ϕ) * (R - p) / c - θ < 0 := by linarith [hθ.1]
        linarith
      have hD0' : s.lamD = 0 := by
        by_contra h'
        have := (tdeliv (lt_of_le_of_ne hD0 (Ne.symm h'))).1; linarith
      refine ⟨hD0', ?_⟩
      have : s.lam0W + s.lam1W = L - s.lamD := by rw [hL]; ring
      rw [this, hD0']; linarith
  · -- region 2
    obtain ⟨hp1, hp2⟩ := hp
    set a := R - p with ha
    have hϕμ : 0 < ϕ / μ := div_pos hϕ hμ
    have ha0 : ϕ / μ ≤ a := by rw [ha]; linarith
    have hapos : 0 < a := by linarith
    have hac : a < c / (μ - Λ1) := by rw [ha]; linarith
    -- if W ≥ 0 then L < Λ1
    have hWL : 0 ≤ a - c / e → L < Λ1 := by
      intro h
      have h1 : c / e ≤ a := by linarith
      have h2 : c / e < c / (μ - Λ1) := lt_of_le_of_lt h1 hac
      have h3 : μ - Λ1 < e := by
        by_contra h'; push_neg at h'
        have := div_le_div_of_nonneg_left hc.le he h'
        linarith
      linarith
    -- D is antitone in L
    have hDmono : ∀ x : ℝ, x < Λ1 → 0 ≤ x → a - θ - ϕ / (μ - Λ1) < a - θ - ϕ / (μ - x) := by
      intro x hx _
      have : ϕ / (μ - x) < ϕ / (μ - Λ1) := div_lt_div_of_pos_left hϕ (by linarith) (by linarith)
      linarith
    have hL0 : 0 ≤ L := by rw [hL]; linarith
    refine ⟨fun hθ => ?_, fun hθ => ?_, fun hθ hpc => ?_⟩
    · -- (2a)
      obtain ⟨hθ0, hθm⟩ := hθ
      have hθa : θ ≤ a - ϕ / (μ - Λ1) := by
        rcases le_total (a - ϕ / (μ - Λ1)) 0 with h | h
        · rw [max_eq_right h] at hθm; linarith
        · rw [max_eq_left h] at hθm; exact hθm
      have hW : a - c / e < 0 := by
        by_contra h; push_neg at h
        have hlt := hWL h
        have hsum : s.lamD + s.lam1W < Λ1 := by linarith
        have := (tbal hsum).1
        have := hDmono L hlt hL0
        linarith
      obtain ⟨h0, h1⟩ := G2 hW
      have hLD : L = s.lamD := by rw [hL, h0, h1]; ring
      have hD1 : s.lamD = Λ1 := by
        by_contra h'
        have hlt : s.lamD + s.lam1W < Λ1 := by
          rw [h1, add_zero]; exact lt_of_le_of_ne (by linarith) h'
        have := (tbal hlt).1
        have := hDmono L (by linarith) hL0
        linarith
      exact ⟨hD1, by rw [h0, h1]; ring⟩
    · -- (2b)
      obtain ⟨hθm, hθM⟩ := hθ
      have hθa : a - ϕ / (μ - Λ1) < θ := lt_of_le_of_lt (le_max_left _ _) hθm
      have hθ0 : 0 < θ := lt_of_le_of_lt (le_max_right _ _) hθm
      have hθc : θ ≤ (c - ϕ) * a / c := le_trans hθM (min_le_left _ _)
      have hθμ : θ ≤ a - ϕ / μ := le_trans hθM (min_le_right _ _)
      have haθ : 0 < a - θ := by linarith
      -- target: L solves D = 0 and walk-ins vanish
      have hDΛ : a - θ - ϕ / (μ - Λ1) < 0 := by linarith
      suffices hfin : s.lam0W = 0 ∧ s.lam1W = 0 ∧ a - θ - ϕ / e = 0 by
        obtain ⟨h0, h1, hD⟩ := hfin
        have hLD : L = s.lamD := by rw [hL, h0, h1]; ring
        refine ⟨?_, by rw [h0, h1]; ring⟩
        have : ϕ / e = a - θ := by linarith
        have he2 : e = ϕ / (a - θ) := by field_simp at this ⊢; linarith
        linarith
      rcases lt_or_ge (a - c / e) 0 with hW | hW
      · obtain ⟨h0, h1⟩ := G2 hW
        have hLD : L = s.lamD := by rw [hL, h0, h1]; ring
        refine ⟨h0, h1, ?_⟩
        rcases lt_or_eq_of_le hD0 with hpos | hzero
        · have hD := (tdeliv hpos).1
          have hlt : s.lamD < Λ1 := by
            by_contra h'; push_neg at h'
            have hge : s.lamD = Λ1 := le_antisymm (by linarith) h'
            have : L = Λ1 := by linarith
            rw [he_def, this] at hD
            linarith
          have := (tbal (by rw [h1, add_zero]; exact hlt)).1
          linarith
        · have hL0' : L = 0 := by rw [hLD, ← hzero]
          have := (tbal (by rw [h1, ← hzero]; linarith)).1
          rw [he_def, hL0', sub_zero] at this
          have : θ = a - ϕ / μ := by linarith
          rw [he_def, hL0', sub_zero, this]; ring
      · have hlt := hWL hW
        have hW' : a - c / e = 0 := le_antisymm G1 hW
        have hce : c / e = a := by linarith
        have he_eq : e = c / a := by field_simp at hce ⊢; linarith
        have hDW : (a - θ - ϕ / e) - (a - c / e) = (c - ϕ) * a / c - θ := by
          rw [he_eq]; field_simp; ring
        have hDnn : 0 ≤ a - θ - ϕ / e := by linarith
        have hsum : s.lamD + s.lam1W < Λ1 := by linarith
        obtain ⟨hDle, -, htie⟩ := tbal hsum
        have hD : a - θ - ϕ / e = 0 := le_antisymm hDle hDnn
        have h0 := htie ⟨by linarith, by linarith⟩
        have h1 : s.lam1W = 0 := by
          by_contra h'
          have := (twalk (lt_of_le_of_ne h1W0 (Ne.symm h'))).2; linarith
        exact ⟨h0, h1, hD⟩
    · -- (2c)
      have hac' : c / μ ≤ a := by rw [ha]; linarith
      have hD0' : s.lamD = 0 := by
        by_contra h'
        obtain ⟨hD, hWD⟩ := tdeliv (lt_of_le_of_ne hD0 (Ne.symm h'))
        -- θ ≤ a - ϕ/μ and θ ≤ (c-ϕ)a/c
        have h1 : ϕ / μ ≤ ϕ / e := div_le_div_of_nonneg_left hϕ.le he (by linarith)
        have hθ1 : θ ≤ a - ϕ / μ := by linarith
        have hθ2 : θ ≤ (c - ϕ) * a / c := by
          have k1 : θ ≤ (c - ϕ) / e := by
            have : (c - ϕ) / e = c / e - ϕ / e := by ring
            linarith
          have k2 : ϕ / e ≤ a - θ := by linarith
          have k3 : θ * ϕ ≤ (c - ϕ) * (a - θ) := by
            have : θ * e ≤ c - ϕ := by rwa [le_div_iff₀ he] at k1
            have : ϕ ≤ (a - θ) * e := by rwa [div_le_iff₀ he] at k2
            nlinarith
          rw [le_div_iff₀ hc]; nlinarith
        rcases le_total ((c - ϕ) * a / c) (a - ϕ / μ) with h | h
        · rw [min_eq_left h] at hθ; linarith
        · rw [min_eq_right h] at hθ; linarith
      refine ⟨hD0', ?_⟩
      have hW : a - c / e = 0 := by
        rcases G1.lt_or_eq with h | h
        · obtain ⟨h0, h1⟩ := G2 h
          have hL0' : L = 0 := by rw [hL, h0, h1, hD0']; ring
          rw [he_def, hL0', sub_zero] at h
          linarith
        · exact h
      have hce : c / e = a := by linarith
      have he_eq : e = c / a := by field_simp at hce ⊢; linarith
      have : s.lam0W + s.lam1W = L - s.lamD := by rw [hL]; ring
      rw [this, hD0']; linarith
