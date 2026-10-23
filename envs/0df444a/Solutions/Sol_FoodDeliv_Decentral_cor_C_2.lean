-- Prove2me | solution 1 for FoodDeliv.Decentral.cor_C_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:21:43.294222+00:00
-- url     : https://prove2.me/submissions/a1a6cef1-e959-4939-a0c7-6aceb7a4536b

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open Set FoodDeliv.Decentral

set_option maxHeartbeats 1000000 in
theorem g80c2 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (p θ : ℝ) (s : Profile)
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
    by_contra h; push Not at h
    have : ¬ s.lam0W < Λ0 := fun hlt => by linarith [tbalk hlt]
    push Not at this
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
        by_contra h'; push Not at h'
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
        by_contra h; push Not at h
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
            by_contra h'; push Not at h'
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


theorem g81_lamD_le (P : Params) {p θ : ℝ} {s : Profile} (hs : IsCustEq P p θ s) :
    s.lamD ≤ P.Λ1 := by
  linarith [hs.tech_le, hs.lam1W_nonneg]

/-- Delivery is used only if it gives nonnegative utility: `λ_D ≤ μ - ϕ/(R-p-θ)`. -/
theorem g81_A (P : Params) (_hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hD : 0 < s.lamD) :
    0 < P.R - p - θ ∧ s.lamD ≤ P.μ - P.ϕ / (P.R - p - θ) := by
  have h := (hs.tech_deliv hD).1
  simp only [UD] at h
  have htot := hs.total_lt
  have hLD : s.lamD ≤ s.total := by
    simp only [Profile.total, Profile.lamW]; linarith [hs.lam1W_nonneg, hs.lam0W_nonneg]
  have he : 0 < P.μ - s.total := by linarith
  have hq : 0 < P.ϕ / (P.μ - s.total) := div_pos hϕ he
  have hx : 0 < P.R - p - θ := by linarith
  refine ⟨hx, ?_⟩
  have : P.ϕ / (P.R - p - θ) ≤ P.μ - s.total := by
    rw [div_le_iff₀ hx]
    have h2 : P.ϕ ≤ (P.R - p - θ) * (P.μ - s.total) := by
      have := (div_le_iff₀ he).1 (show P.ϕ / (P.μ - s.total) ≤ P.R - p - θ by linarith)
      linarith
    linarith
  linarith

theorem g81_A0 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : P.R - p - P.ϕ / P.μ < θ) : s.lamD = 0 := by
  by_contra hne
  have hD : 0 < s.lamD := lt_of_le_of_ne hs.lamD_nonneg (Ne.symm hne)
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  have hμ := hP.μ_pos
  have : P.μ < P.ϕ / (P.R - p - θ) := by
    rw [lt_div_iff₀ hx]
    have : P.μ * (P.R - p - θ) < P.μ * (P.ϕ / P.μ) := by
      apply mul_lt_mul_of_pos_left _ hμ; linarith
    rwa [mul_div_cancel₀ _ hμ.ne'] at this
  linarith

/-- AM–GM bound: the platform profit never exceeds `(√(μ r) - √ϕ)²`. -/
theorem g81_B3 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ) :
    θ * s.lamD ≤ (Real.sqrt (P.μ * (P.R - p)) - Real.sqrt P.ϕ) ^ 2 := by
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0]; simp [sq_nonneg]
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  have hμ := hP.μ_pos
  set x := P.R - p - θ with hxdef
  set r := P.R - p with hr
  have hr0 : 0 ≤ r := by linarith
  set u := Real.sqrt (P.μ * r)
  set w := Real.sqrt P.ϕ
  have hu2 : u ^ 2 = P.μ * r := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = P.ϕ := Real.sq_sqrt hϕ.le
  have key : 0 ≤ P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r := by
    have h1 : P.μ * (P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r) = (P.μ * x - u * w) ^ 2 := by
      have : (u * w) ^ 2 = P.μ * r * P.ϕ := by rw [mul_pow, hu2, hw2]
      nlinarith [this]
    have h2 : 0 ≤ P.μ * (P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r) := by rw [h1]; positivity
    exact (mul_nonneg_iff_of_pos_left hμ).1 h2
  calc θ * s.lamD ≤ θ * (P.μ - P.ϕ / x) := mul_le_mul_of_nonneg_left hle hθ
    _ = (r - x) * (P.μ * x - P.ϕ) / x := by
        have : θ = r - x := by rw [hxdef, hr]; ring
        rw [this]; field_simp
    _ ≤ (u - w) ^ 2 := by
        rw [div_le_iff₀ hx]
        have : (u - w) ^ 2 * x - (r - x) * (P.μ * x - P.ϕ) = P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r := by
          linear_combination x * hu2 + x * hw2
        linarith

theorem g81_B1 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ) (hp : p ≤ P.R - P.c / (P.μ - P.Λ1)) :
    θ * s.lamD ≤ (P.c - P.ϕ) * (P.R - p) / P.c * P.Λ1 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hc := hP.c_pos
  have hr : 0 < P.R - p := by have := div_pos hc hm; linarith
  have hθc : 0 ≤ (P.c - P.ϕ) * (P.R - p) / P.c :=
    div_nonneg (mul_nonneg (by linarith [hP.ϕ_lt_c]) hr.le) hc.le
  have hΛ := hP.Λ1_pos
  have hD0 := hs.lamD_nonneg
  by_cases h1 : θ ≤ (P.c - P.ϕ) * (P.R - p) / P.c
  · have := g81_lamD_le P hs
    calc θ * s.lamD ≤ θ * P.Λ1 := mul_le_mul_of_nonneg_left this hθ
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hΛ.le
  · push Not at h1
    have hD : s.lamD = 0 := by
      by_cases h2 : θ ≤ P.R - p - P.ϕ / P.μ
      · exact (((g80c2 P hP hϕ p θ s hs).1 hp).2 ⟨h1, h2⟩).1
      · push Not at h2; exact g81_A0 P hP hϕ hs h2
    rw [hD, mul_zero]; positivity

theorem g81_B2A (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ)
    (hp : p ≤ P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2) :
    θ * s.lamD ≤ (P.R - p - P.ϕ / (P.μ - P.Λ1)) * P.Λ1 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hΛ := hP.Λ1_pos
  set m := P.μ - P.Λ1 with hmdef
  set r := P.R - p with hrdef
  set x1 := P.ϕ / m with hx1
  have hx1m : x1 * m = P.ϕ := by rw [hx1]; field_simp
  have hrm : P.μ * P.ϕ ≤ r * m ^ 2 := by
    have : P.μ * P.ϕ / m ^ 2 ≤ r := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hx1pos : 0 < x1 := div_pos hϕ hm
  have hrx1 : x1 ≤ r := by
    -- r m^2 ≥ μ ϕ ≥ m ϕ = m^2 x1
    have : m ^ 2 * x1 ≤ r * m ^ 2 := by
      have : m ^ 2 * x1 = m * P.ϕ := by rw [← hx1m]; ring
      rw [this]; nlinarith
    nlinarith [sq_pos_of_pos hm]
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0, mul_zero]; nlinarith
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  by_cases h1 : θ ≤ r - x1
  · calc θ * s.lamD ≤ θ * P.Λ1 := mul_le_mul_of_nonneg_left (g81_lamD_le P hs) hθ
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hΛ.le
  · push Not at h1
    set x := P.R - p - θ with hxdef
    have hxlt : x < x1 := by rw [hxdef]; linarith
    have hθx : θ = r - x := by rw [hxdef, hrdef]; ring
    calc θ * s.lamD ≤ θ * (P.μ - P.ϕ / x) := mul_le_mul_of_nonneg_left hle hθ
      _ = (r - x) * (P.μ * x - P.ϕ) / x := by rw [hθx]; field_simp
      _ ≤ _ := by
        rw [div_le_iff₀ hx]
        have hid : (r - x1) * P.Λ1 * x - (r - x) * (P.μ * x - P.ϕ) = (x1 - x) * (r * m - P.μ * x) := by
          rw [← hx1m, hmdef]; ring
        have h3 : P.μ * x ≤ r * m := by
          have : P.μ * x1 ≤ r * m := by
            have : P.μ * x1 * m ≤ r * m * m := by
              rw [mul_assoc, hx1m]; nlinarith
            exact le_of_mul_le_mul_right this hm
          nlinarith
        have : 0 ≤ (x1 - x) * (r * m - P.μ * x) := mul_nonneg (by linarith) (by linarith)
        linarith

theorem g81_B2B (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ)
    (hp1 : P.R - P.c / (P.μ - P.Λ1) < p) (hp : p ≤ P.R - P.c ^ 2 / (P.μ * P.ϕ)) :
    θ * s.lamD ≤ (P.c - P.ϕ) * (P.R - p) / P.c * (P.μ - P.c / (P.R - p)) := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  set r := P.R - p with hrdef
  have hrc : P.c ^ 2 ≤ r * (P.μ * P.ϕ) := by
    have : P.c ^ 2 / (P.μ * P.ϕ) ≤ r := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hr : 0 < r := by
    by_contra h; push Not at h
    have : r * (P.μ * P.ϕ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    nlinarith
  -- c/μ ≤ r
  have hcr : P.c ≤ P.μ * r := by
    by_contra h; push Not at h
    have : P.c ^ 2 ≤ r * P.μ * P.ϕ := by linarith
    have : r * P.μ * P.ϕ < P.c * P.c := by
      calc r * P.μ * P.ϕ = (P.μ * r) * P.ϕ := by ring
        _ < P.c * P.c := by
          apply mul_lt_mul'' h hϕc (by positivity) hϕ.le
    nlinarith
  have hV0 : 0 ≤ (P.c - P.ϕ) * r / P.c * (P.μ - P.c / r) := by
    apply mul_nonneg (div_nonneg (mul_nonneg (by linarith) hr.le) hc.le)
    rw [sub_nonneg, div_le_iff₀ hr]; linarith
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0, mul_zero]; exact hV0
  by_cases h1 : (P.c - P.ϕ) * r / P.c < θ
  · have hrϕ : p ≤ P.R - P.ϕ / P.μ := by
      have : P.ϕ / P.μ ≤ r := by
        rw [div_le_iff₀ hμ]; nlinarith
      linarith
    have hrcμ : p ≤ P.R - P.c / P.μ := by
      have : P.c / P.μ ≤ r := by rw [div_le_iff₀ hμ]; linarith
      linarith
    have := ((((g80c2 P hP hϕ p θ s hs).2 ⟨hp1, hrϕ⟩).2.2 (min_lt_of_left_lt h1)) hrcμ).1
    linarith
  push Not at h1
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  set x := P.R - p - θ with hxdef
  have hθx : θ = r - x := by rw [hxdef, hrdef]; ring
  have hxc : P.ϕ * r ≤ P.c * x := by
    have : P.ϕ * r / P.c ≤ x := by
      have : (P.c - P.ϕ) * r / P.c = r - P.ϕ * r / P.c := by field_simp
      rw [hθx] at h1; linarith
    rwa [div_le_iff₀ hc, mul_comm x] at this
  have hxμ : P.c ≤ P.μ * x := by
    -- μ x c ≥ μ ϕ r ≥ c^2
    have : P.c * P.c ≤ P.c * (P.μ * x) := by nlinarith
    exact le_of_mul_le_mul_left this hc
  calc θ * s.lamD ≤ θ * (P.μ - P.ϕ / x) := mul_le_mul_of_nonneg_left hle hθ
    _ = (r - x) * (P.μ * x - P.ϕ) / x := by rw [hθx]; field_simp
    _ ≤ _ := by
      rw [div_le_iff₀ hx]
      have hid : (P.c - P.ϕ) * r / P.c * (P.μ - P.c / r) * x - (r - x) * (P.μ * x - P.ϕ) =
          (P.c * x - P.ϕ * r) * (P.μ * x - P.c) / P.c := by
        field_simp; ring
      have : 0 ≤ (P.c * x - P.ϕ * r) * (P.μ * x - P.c) / P.c :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) hc.le
      linarith

theorem g81_br {σ : ℝ → ℝ → Profile} {p θk V : ℝ} (hθk : 0 ≤ θk)
    (hval : θk * (σ p θk).lamD = V) (hb : ∀ θ', 0 ≤ θ' → θ' * (σ p θ').lamD ≤ V) :
    IsFeeBR σ p θk :=
  ⟨hθk, fun θ' h => by simp only [platProfit]; rw [hval]; exact hb θ' h⟩

theorem g81_R1 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (σ : ℝ → ℝ → Profile) (p : ℝ)
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq P p θ (σ p θ)) (hp : p ≤ P.R - P.c / (P.μ - P.Λ1)) :
    IsFeeBR σ p ((P.c - P.ϕ) * (P.R - p) / P.c) ∧
    (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamD = P.Λ1 ∧
    (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamW = P.μ - P.c / (P.R - p) - P.Λ1 ∧
    platProfit σ p ((P.c - P.ϕ) * (P.R - p) / P.c) = (P.c - P.ϕ) * (P.R - p) / P.c * P.Λ1 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hc := hP.c_pos
  have hr : 0 < P.R - p := by have := div_pos hc hm; linarith
  have hθc : 0 < (P.c - P.ϕ) * (P.R - p) / P.c :=
    div_pos (mul_pos (by linarith [hP.ϕ_lt_c]) hr) hc
  have h := ((g80c2 P hP hϕ p _ _ (hσ _ hθc.le)).1 hp).1 ⟨hθc, le_rfl⟩
  have hv : platProfit σ p ((P.c - P.ϕ) * (P.R - p) / P.c) = (P.c - P.ϕ) * (P.R - p) / P.c * P.Λ1 := by
    simp only [platProfit]; rw [h.1]
  refine ⟨g81_br hθc.le (by rw [h.1]) (fun θ' h' => g81_B1 P hP hϕ (hσ θ' h') h' hp), h.1, h.2, hv⟩

theorem g81_R2A (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (σ : ℝ → ℝ → Profile) (p : ℝ)
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq P p θ (σ p θ))
    (hp1 : P.R - P.c / (P.μ - P.Λ1) < p) (hp : p ≤ P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2) :
    IsFeeBR σ p (P.R - p - P.ϕ / (P.μ - P.Λ1)) ∧
    (σ p (P.R - p - P.ϕ / (P.μ - P.Λ1))).lamD = P.Λ1 ∧
    (σ p (P.R - p - P.ϕ / (P.μ - P.Λ1))).lamW = 0 ∧
    platProfit σ p (P.R - p - P.ϕ / (P.μ - P.Λ1)) = (P.R - p - P.ϕ / (P.μ - P.Λ1)) * P.Λ1 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hΛ := hP.Λ1_pos
  have hlt : P.ϕ / (P.μ - P.Λ1) < P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 := by
    rw [div_lt_div_iff₀ hm (by positivity)]
    nlinarith [mul_pos hϕ hΛ, mul_pos (mul_pos hϕ hΛ) hm]
  have hle2 : P.ϕ / P.μ ≤ P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 := by
    rw [div_le_div_iff₀ hμ (by positivity)]
    have : (P.μ - P.Λ1) ^ 2 ≤ P.μ * P.μ := by nlinarith
    nlinarith
  have hθ1 : 0 < P.R - p - P.ϕ / (P.μ - P.Λ1) := by linarith
  have h := ((g80c2 P hP hϕ p _ _ (hσ _ hθ1.le)).2 ⟨hp1, by linarith⟩).1 ⟨hθ1, le_max_left _ _⟩
  have hv : platProfit σ p (P.R - p - P.ϕ / (P.μ - P.Λ1)) = (P.R - p - P.ϕ / (P.μ - P.Λ1)) * P.Λ1 := by
    simp only [platProfit]; rw [h.1]
  exact ⟨g81_br hθ1.le (by rw [h.1]) (fun θ' h' => g81_B2A P hP hϕ (hσ θ' h') h' hp), h.1, h.2, hv⟩

theorem g81_R2B (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (σ : ℝ → ℝ → Profile) (p : ℝ)
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq P p θ (σ p θ))
    (hp1 : P.R - P.c / (P.μ - P.Λ1) < p) (hp : p ≤ P.R - P.c ^ 2 / (P.μ * P.ϕ)) :
    IsFeeBR σ p ((P.c - P.ϕ) * (P.R - p) / P.c) ∧
    (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamD = P.μ - P.c / (P.R - p) ∧
    (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamW = 0 ∧
    platProfit σ p ((P.c - P.ϕ) * (P.R - p) / P.c) =
      (P.c - P.ϕ) * (P.R - p) / P.c * (P.μ - P.c / (P.R - p)) := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  set r := P.R - p with hrdef
  have hrc : P.c ^ 2 ≤ r * (P.μ * P.ϕ) := by
    have : P.c ^ 2 / (P.μ * P.ϕ) ≤ r := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hr : 0 < r := by
    by_contra h; push Not at h
    have : r * (P.μ * P.ϕ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    nlinarith
  have hcr : P.c ≤ P.μ * r := by
    by_contra h; push Not at h
    have : r * P.μ * P.ϕ < P.c * P.c := by
      calc r * P.μ * P.ϕ = (P.μ * r) * P.ϕ := by ring
        _ < P.c * P.c := mul_lt_mul'' h hϕc (by positivity) hϕ.le
    nlinarith
  have hrm : r * (P.μ - P.Λ1) < P.c := by
    have : r < P.c / (P.μ - P.Λ1) := by linarith
    rwa [lt_div_iff₀ hm] at this
  have hθc : 0 < (P.c - P.ϕ) * r / P.c := div_pos (mul_pos (by linarith) hr) hc
  have hθ1 : P.R - p - P.ϕ / (P.μ - P.Λ1) < (P.c - P.ϕ) * r / P.c := by
    rw [← hrdef]
    have e1 : (P.c - P.ϕ) * r / P.c = r - P.ϕ * r / P.c := by field_simp
    rw [e1]
    have : P.ϕ * r / P.c < P.ϕ / (P.μ - P.Λ1) := by
      rw [div_lt_div_iff₀ hc hm]; nlinarith
    linarith
  have hθc2 : (P.c - P.ϕ) * r / P.c ≤ r - P.ϕ / P.μ := by
    have e1 : (P.c - P.ϕ) * r / P.c = r - P.ϕ * r / P.c := by field_simp
    rw [e1]
    have : P.ϕ / P.μ ≤ P.ϕ * r / P.c := by
      rw [div_le_div_iff₀ hμ hc]; nlinarith
    linarith
  have hpϕ : p ≤ P.R - P.ϕ / P.μ := by
    have : 0 ≤ (P.c - P.ϕ) * r / P.c := hθc.le
    linarith
  have h := ((g80c2 P hP hϕ p _ _ (hσ _ hθc.le)).2 ⟨hp1, hpϕ⟩).2.1
    ⟨max_lt hθ1 hθc, le_min le_rfl hθc2⟩
  have hden : P.R - p - (P.c - P.ϕ) * r / P.c = P.ϕ * r / P.c := by
    rw [← hrdef]; field_simp; ring
  have hD : (σ p ((P.c - P.ϕ) * r / P.c)).lamD = P.μ - P.c / r := by
    rw [h.1, hden]; congr 1; field_simp
  have hv : platProfit σ p ((P.c - P.ϕ) * r / P.c) = (P.c - P.ϕ) * r / P.c * (P.μ - P.c / r) := by
    simp only [platProfit]; rw [hD]
  exact ⟨g81_br hθc.le (by rw [hD]) (fun θ' h' => g81_B2B P hP hϕ (hσ θ' h') h' hp1 hp), hD, h.2, hv⟩

theorem g81_R3 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (σ : ℝ → ℝ → Profile) (p : ℝ)
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq P p θ (σ p θ))
    (hr1 : P.ϕ / P.μ ≤ P.R - p) (hr2 : P.R - p < P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2)
    (hr3 : P.R - p ≤ P.c ^ 2 / (P.μ * P.ϕ)) (hr4 : P.R - p < P.c / (P.μ - P.Λ1)) :
    IsFeeBR σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ) ∧
    (σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ)).lamD =
      P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p)) ∧
    (σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ)).lamW = 0 ∧
    platProfit σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ) =
      (Real.sqrt (P.μ * (P.R - p)) - Real.sqrt P.ϕ) ^ 2 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  set r := P.R - p with hrdef
  have hr : 0 < r := lt_of_lt_of_le (div_pos hϕ hμ) hr1
  set u := Real.sqrt (P.μ * r) with hudef
  set w := Real.sqrt P.ϕ with hwdef
  have hu2 : u ^ 2 = P.μ * r := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = P.ϕ := Real.sq_sqrt hϕ.le
  have hu : 0 < u := Real.sqrt_pos.2 (by positivity)
  have hw : 0 < w := Real.sqrt_pos.2 hϕ
  have hsq : Real.sqrt (P.μ * P.ϕ * r) = u * w := by
    rw [show P.μ * P.ϕ * r = P.μ * r * P.ϕ by ring, Real.sqrt_mul (by positivity)]
  rw [hsq]
  set xs := u * w / P.μ with hxs
  have hxs0 : 0 < xs := by positivity
  have hxs2 : xs ^ 2 = P.ϕ * r / P.μ := by
    rw [hxs, div_pow, mul_pow, hu2, hw2]; field_simp
  -- the value
  have hval : (r - xs) * (P.μ - P.ϕ / xs) = (u - w) ^ 2 := by
    rw [hxs, ← hw2]
    have : r = u ^ 2 / P.μ := by rw [hu2]; field_simp
    rw [this]; field_simp
  have hsq2 : Real.sqrt (P.μ * P.ϕ / r) = P.ϕ / xs := by
    have h1 : P.μ * P.ϕ / r = (P.ϕ / xs) ^ 2 := by
      rw [div_pow, hxs2]; field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  rw [hsq2]
  have hbound : ∀ θ', 0 ≤ θ' → θ' * (σ p θ').lamD ≤ (u - w) ^ 2 :=
    fun θ' h' => g81_B3 P hP hϕ (hσ θ' h') h'
  rcases eq_or_lt_of_le hr1 with heq | hlt
  · -- boundary `r = ϕ/μ`: zero fee, nobody joins
    have hrr : P.μ * r = P.ϕ := by rw [← heq]; field_simp
    have huw : u = w := by rw [hudef, hrr]
    have hxr : xs = r := by
      rw [hxs, huw, ← sq, hw2, ← heq]
    have hθ0 : r - xs = 0 := by rw [hxr]; ring
    rw [hθ0]
    have hs := hσ 0 le_rfl
    have hD : (σ p 0).lamD = 0 := by
      by_contra hne
      have hD : 0 < (σ p 0).lamD := lt_of_le_of_ne hs.lamD_nonneg (Ne.symm hne)
      obtain ⟨-, hle⟩ := g81_A P hP hϕ hs hD
      rw [← hrdef, sub_zero, ← heq, div_div_cancel₀ hϕ.ne'] at hle
      · linarith
    have hUW : UW P p (σ p 0).total < 0 := by
      simp only [UW]
      have htot := hs.total_lt
      have hL : 0 ≤ (σ p 0).total := by
        simp only [Profile.total, Profile.lamW]
        linarith [hs.lamD_nonneg, hs.lam0W_nonneg, hs.lam1W_nonneg]
      have he : 0 < P.μ - (σ p 0).total := by linarith
      have : P.c / P.μ ≤ P.c / (P.μ - (σ p 0).total) :=
        div_le_div_of_nonneg_left hc.le he (by linarith)
      have : P.ϕ / P.μ < P.c / P.μ := div_lt_div_of_pos_right hϕc hμ
      rw [← hrdef]; linarith
    have h0W : (σ p 0).lam0W = 0 := by
      by_contra hne
      have := hs.trad_join (lt_of_le_of_ne hs.lam0W_nonneg (Ne.symm hne)); linarith
    have h1W : (σ p 0).lam1W = 0 := by
      by_contra hne
      have := (hs.tech_walk (lt_of_le_of_ne hs.lam1W_nonneg (Ne.symm hne))).1; linarith
    have hval0 : (u - w) ^ 2 = 0 := by rw [huw]; ring
    refine ⟨g81_br le_rfl (by rw [hD, hval0]; ring) hbound, ?_, ?_, ?_⟩
    · rw [hD, hxr, ← heq]; field_simp; ring
    · simp [Profile.lamW, h0W, h1W]
    · simp only [platProfit]; rw [hD, hval0]; ring
  · -- interior
    have hxr : xs < r := by
      have : xs ^ 2 < r ^ 2 := by
        rw [hxs2, div_lt_iff₀ hμ]
        have : P.ϕ < P.μ * r := by rwa [div_lt_iff₀ hμ, mul_comm] at hlt
        nlinarith
      nlinarith
    have hθpos : 0 < r - xs := by linarith
    have hx1 : xs < P.ϕ / (P.μ - P.Λ1) := by
      have h0 : 0 < P.ϕ / (P.μ - P.Λ1) := div_pos hϕ hm
      refine (pow_lt_pow_iff_left₀ hxs0.le h0.le two_ne_zero).1 ?_
      rw [hxs2, div_pow, div_lt_div_iff₀ hμ (by positivity)]
      have h1 : r * (P.μ - P.Λ1) ^ 2 < P.μ * P.ϕ := by
        rwa [lt_div_iff₀ (by positivity)] at hr2
      have h2 := mul_lt_mul_of_pos_left h1 hϕ
      nlinarith [h2]
    have hxc : P.ϕ * r / P.c ≤ xs := by
      have h0 : 0 ≤ P.ϕ * r / P.c := by positivity
      refine (pow_le_pow_iff_left₀ h0 hxs0.le two_ne_zero).1 ?_
      rw [hxs2, div_pow, div_le_div_iff₀ (by positivity) hμ]
      have h1 : r * (P.μ * P.ϕ) ≤ P.c ^ 2 := by
        rwa [le_div_iff₀ (by positivity)] at hr3
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ P.ϕ * r by positivity)
      have e : (P.ϕ * r) ^ 2 * P.μ = P.ϕ * r * (r * (P.μ * P.ϕ)) := by ring
      rw [e]; linarith
    have hxμ : P.ϕ / P.μ ≤ xs := by
      have h0 : 0 ≤ P.ϕ / P.μ := by positivity
      refine (pow_le_pow_iff_left₀ h0 hxs0.le two_ne_zero).1 ?_
      rw [hxs2, div_pow, div_le_div_iff₀ (by positivity) hμ]
      have h1 : P.ϕ ≤ P.μ * r := by rwa [div_le_iff₀ hμ, mul_comm] at hr1
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ P.ϕ * P.μ by positivity)
      have e1 : P.ϕ ^ 2 * P.μ = P.ϕ * P.μ * P.ϕ := by ring
      have e2 : P.ϕ * r * P.μ ^ 2 = P.ϕ * P.μ * (P.μ * r) := by ring
      rw [e1, e2]; exact h2
    have hpϕ : p ≤ P.R - P.ϕ / P.μ := by linarith
    have hp1 : P.R - P.c / (P.μ - P.Λ1) < p := by linarith
    have hθc : r - xs ≤ (P.c - P.ϕ) * r / P.c := by
      have e1 : (P.c - P.ϕ) * r / P.c = r - P.ϕ * r / P.c := by field_simp
      rw [e1]; linarith
    have h := ((g80c2 P hP hϕ p _ _ (hσ _ hθpos.le)).2 ⟨hp1, hpϕ⟩).2.1
      ⟨max_lt (by rw [← hrdef]; linarith) hθpos, le_min hθc (by rw [← hrdef]; linarith)⟩
    have hden : P.R - p - (r - xs) = xs := by rw [← hrdef]; ring
    rw [hden] at h
    have hv : (r - xs) * (σ p (r - xs)).lamD = (u - w) ^ 2 := by rw [h.1, hval]
    exact ⟨g81_br hθpos.le hv hbound, h.1, h.2, by simp only [platProfit]; exact hv⟩


theorem g81_B1s (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ) (hp : p ≤ P.R - P.c / (P.μ - P.Λ1))
    (hne : θ ≠ (P.c - P.ϕ) * (P.R - p) / P.c) :
    θ * s.lamD < (P.c - P.ϕ) * (P.R - p) / P.c * P.Λ1 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hc := hP.c_pos
  have hr : 0 < P.R - p := by have := div_pos hc hm; linarith
  have hθc : 0 < (P.c - P.ϕ) * (P.R - p) / P.c :=
    div_pos (mul_pos (by linarith [hP.ϕ_lt_c]) hr) hc
  have hΛ := hP.Λ1_pos
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := g81_lamD_le P hs
    calc θ * s.lamD ≤ θ * P.Λ1 := mul_le_mul_of_nonneg_left this hθ
      _ < _ := mul_lt_mul_of_pos_right h1 hΛ
  · have hD : s.lamD = 0 := by
      by_cases h2 : θ ≤ P.R - p - P.ϕ / P.μ
      · exact (((g80c2 P hP hϕ p θ s hs).1 hp).2 ⟨h1, h2⟩).1
      · push Not at h2; exact g81_A0 P hP hϕ hs h2
    rw [hD, mul_zero]; positivity

theorem g81_B2As (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ)
    (hp : p ≤ P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2) (hne : θ ≠ P.R - p - P.ϕ / (P.μ - P.Λ1)) :
    θ * s.lamD < (P.R - p - P.ϕ / (P.μ - P.Λ1)) * P.Λ1 := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hΛ := hP.Λ1_pos
  set m := P.μ - P.Λ1 with hmdef
  set r := P.R - p with hrdef
  set x1 := P.ϕ / m with hx1
  have hx1m : x1 * m = P.ϕ := by rw [hx1]; field_simp
  have hrm : P.μ * P.ϕ ≤ r * m ^ 2 := by
    have : P.μ * P.ϕ / m ^ 2 ≤ r := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hx1pos : 0 < x1 := div_pos hϕ hm
  have hrx1 : x1 < r := by
    have : m ^ 2 * x1 < r * m ^ 2 := by
      have : m ^ 2 * x1 = m * P.ϕ := by rw [← hx1m]; ring
      rw [this]; nlinarith
    nlinarith [sq_pos_of_pos hm]
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0, mul_zero]; nlinarith
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  rcases lt_or_gt_of_ne hne with h1 | h1
  · calc θ * s.lamD ≤ θ * P.Λ1 := mul_le_mul_of_nonneg_left (g81_lamD_le P hs) hθ
      _ < _ := mul_lt_mul_of_pos_right h1 hΛ
  · set x := P.R - p - θ with hxdef
    have hxlt : x < x1 := by rw [hxdef]; linarith
    have hθx : θ = r - x := by rw [hxdef, hrdef]; ring
    calc θ * s.lamD ≤ θ * (P.μ - P.ϕ / x) := mul_le_mul_of_nonneg_left hle hθ
      _ = (r - x) * (P.μ * x - P.ϕ) / x := by rw [hθx]; field_simp
      _ < _ := by
        rw [div_lt_iff₀ hx]
        have hid : (r - x1) * P.Λ1 * x - (r - x) * (P.μ * x - P.ϕ) = (x1 - x) * (r * m - P.μ * x) := by
          rw [← hx1m, hmdef]; ring
        have h3 : P.μ * x < r * m := by
          have : P.μ * x1 ≤ r * m := by
            have : P.μ * x1 * m ≤ r * m * m := by
              rw [mul_assoc, hx1m]; nlinarith
            exact le_of_mul_le_mul_right this hm
          nlinarith
        have : 0 < (x1 - x) * (r * m - P.μ * x) := mul_pos (by linarith) (by linarith)
        linarith

theorem g81_B2Bs (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ)
    (hp1 : P.R - P.c / (P.μ - P.Λ1) < p) (hp : p ≤ P.R - P.c ^ 2 / (P.μ * P.ϕ))
    (hne : θ ≠ (P.c - P.ϕ) * (P.R - p) / P.c) :
    θ * s.lamD < (P.c - P.ϕ) * (P.R - p) / P.c * (P.μ - P.c / (P.R - p)) := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  set r := P.R - p with hrdef
  have hrc : P.c ^ 2 ≤ r * (P.μ * P.ϕ) := by
    have : P.c ^ 2 / (P.μ * P.ϕ) ≤ r := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hr : 0 < r := by
    by_contra h; push Not at h
    have : r * (P.μ * P.ϕ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    nlinarith
  have hcr : P.c < P.μ * r := by
    by_contra h; push Not at h
    have : r * P.μ * P.ϕ < P.c * P.c := by
      calc r * P.μ * P.ϕ = (P.μ * r) * P.ϕ := by ring
        _ < P.c * P.c := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h hϕc hϕ.le hc
    nlinarith
  have hV0 : 0 < (P.c - P.ϕ) * r / P.c * (P.μ - P.c / r) := by
    apply mul_pos (div_pos (mul_pos (by linarith) hr) hc)
    rw [sub_pos, div_lt_iff₀ hr]; linarith
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0, mul_zero]; exact hV0
  rcases lt_or_gt_of_ne hne with h1 | h1
  swap
  · have hrϕ : p ≤ P.R - P.ϕ / P.μ := by
      have : P.ϕ / P.μ ≤ r := by
        rw [div_le_iff₀ hμ]; nlinarith
      linarith
    have hrcμ : p ≤ P.R - P.c / P.μ := by
      have : P.c / P.μ ≤ r := by rw [div_le_iff₀ hμ]; linarith
      linarith
    have := ((((g80c2 P hP hϕ p θ s hs).2 ⟨hp1, hrϕ⟩).2.2 (min_lt_of_left_lt h1)) hrcμ).1
    linarith
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  set x := P.R - p - θ with hxdef
  have hθx : θ = r - x := by rw [hxdef, hrdef]; ring
  have hxc : P.ϕ * r < P.c * x := by
    have : P.ϕ * r / P.c < x := by
      have : (P.c - P.ϕ) * r / P.c = r - P.ϕ * r / P.c := by field_simp
      rw [hθx] at h1; linarith
    rwa [div_lt_iff₀ hc, mul_comm x] at this
  have hxμ : P.c < P.μ * x := by
    have : P.c * P.c < P.c * (P.μ * x) := by nlinarith
    exact lt_of_mul_lt_mul_left this hc.le
  calc θ * s.lamD ≤ θ * (P.μ - P.ϕ / x) := mul_le_mul_of_nonneg_left hle hθ
    _ = (r - x) * (P.μ * x - P.ϕ) / x := by rw [hθx]; field_simp
    _ < _ := by
      rw [div_lt_iff₀ hx]
      have hid : (P.c - P.ϕ) * r / P.c * (P.μ - P.c / r) * x - (r - x) * (P.μ * x - P.ϕ) =
          (P.c * x - P.ϕ * r) * (P.μ * x - P.c) / P.c := by
        field_simp; ring
      have : 0 < (P.c * x - P.ϕ * r) * (P.μ * x - P.c) / P.c :=
        div_pos (mul_pos (by linarith) (by linarith)) hc
      linarith

theorem g81_B3s (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ) (hr1 : P.ϕ / P.μ < P.R - p)
    (hne : θ ≠ P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ) :
    θ * s.lamD < (Real.sqrt (P.μ * (P.R - p)) - Real.sqrt P.ϕ) ^ 2 := by
  have hμ := hP.μ_pos
  set r := P.R - p with hr
  have hr0 : 0 < r := lt_trans (div_pos hϕ hμ) hr1
  set u := Real.sqrt (P.μ * r)
  set w := Real.sqrt P.ϕ
  have hu2 : u ^ 2 = P.μ * r := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = P.ϕ := Real.sq_sqrt hϕ.le
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hw : 0 < w := Real.sqrt_pos.2 hϕ
  have huw : w < u := Real.sqrt_lt_sqrt hϕ.le (by rwa [div_lt_iff₀ hμ, mul_comm] at hr1)
  have hsq : Real.sqrt (P.μ * P.ϕ * r) = u * w := by
    rw [show P.μ * P.ϕ * r = P.μ * r * P.ϕ by ring, Real.sqrt_mul (by positivity)]
  rw [hsq] at hne
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0, mul_zero]; nlinarith
  obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
  set x := P.R - p - θ with hxdef
  have hxne : P.μ * x - u * w ≠ 0 := by
    intro h; apply hne
    have : x = u * w / P.μ := by field_simp; linarith
    rw [← this, hxdef]; ring
  have key : 0 < P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r := by
    have h1 : P.μ * (P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r) = (P.μ * x - u * w) ^ 2 := by
      have : (u * w) ^ 2 = P.μ * r * P.ϕ := by rw [mul_pow, hu2, hw2]
      nlinarith [this]
    have h2 : 0 < P.μ * (P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r) := by
      rw [h1]; positivity
    exact (mul_pos_iff_of_pos_left hμ).1 h2
  calc θ * s.lamD ≤ θ * (P.μ - P.ϕ / x) := mul_le_mul_of_nonneg_left hle hθ
    _ = (r - x) * (P.μ * x - P.ϕ) / x := by
        have : θ = r - x := by rw [hxdef, hr]; ring
        rw [this]; field_simp
    _ < (u - w) ^ 2 := by
        rw [div_lt_iff₀ hx]
        have : (u - w) ^ 2 * x - (r - x) * (P.μ * x - P.ϕ) = P.μ * x ^ 2 - 2 * u * w * x + P.ϕ * r := by
          linear_combination x * hu2 + x * hw2
        linarith

theorem g81_zero (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) {p θ : ℝ} {s : Profile}
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ) (heq : P.R - p = P.ϕ / P.μ) : s.total = 0 := by
  have hμ := hP.μ_pos
  have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  have hD : s.lamD = 0 := by
    by_contra hne
    have hD : 0 < s.lamD := lt_of_le_of_ne hs.lamD_nonneg (Ne.symm hne)
    obtain ⟨hx, hle⟩ := g81_A P hP hϕ hs hD
    have : P.μ ≤ P.ϕ / (P.R - p - θ) := by
      rw [le_div_iff₀ hx]
      have : P.μ * (P.R - p) = P.ϕ := by rw [heq]; field_simp
      nlinarith
    linarith
  have hUW : UW P p s.total < 0 := by
    simp only [UW]
    have htot := hs.total_lt
    have hL : 0 ≤ s.total := by
      simp only [Profile.total, Profile.lamW]
      linarith [hs.lamD_nonneg, hs.lam0W_nonneg, hs.lam1W_nonneg]
    have he : 0 < P.μ - s.total := by linarith
    have : P.c / P.μ ≤ P.c / (P.μ - s.total) :=
      div_le_div_of_nonneg_left hc.le he (by linarith)
    have : P.ϕ / P.μ < P.c / P.μ := div_lt_div_of_pos_right hϕc hμ
    linarith
  have h0W : s.lam0W = 0 := by
    by_contra hne
    have := hs.trad_join (lt_of_le_of_ne hs.lam0W_nonneg (Ne.symm hne)); linarith
  have h1W : s.lam1W = 0 := by
    by_contra hne
    have := (hs.tech_walk (lt_of_le_of_ne hs.lam1W_nonneg (Ne.symm hne))).1; linarith
  simp [Profile.total, Profile.lamW, hD, h0W, h1W]

theorem g81_uniq {σ : ℝ → ℝ → Profile} {p θk θ : ℝ} (hk : IsFeeBR σ p θk) (h : IsFeeBR σ p θ)
    (hs : θ ≠ θk → θ * (σ p θ).lamD < θk * (σ p θk).lamD) : θ = θk := by
  by_contra hne
  have := hk.2 θ h.1
  have h2 := h.2 θk hk.1
  simp only [platProfit] at this h2
  linarith [hs hne]

theorem solution (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ)
    (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ)
    (hσ : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq P p θ (σ p θ))
    (hfee : ∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) :
    (P.Λ1 ≤ (P.c - P.ϕ) / P.c * P.μ → ∀ p : ℝ, 0 ≤ p →
      (p ≤ P.R - P.c / (P.μ - P.Λ1) →
        restProfit σ fee p = p * (P.μ - P.c / (P.R - p))) ∧
      (P.R - P.c / (P.μ - P.Λ1) < p ∧ p ≤ P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 →
        restProfit σ fee p = p * P.Λ1) ∧
      (P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 < p ∧ p ≤ P.R - P.ϕ / P.μ →
        restProfit σ fee p = p * (P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p))))) ∧
    ((P.c - P.ϕ) / P.c * P.μ < P.Λ1 → ∀ p : ℝ, 0 ≤ p →
      (p ≤ P.R - P.c ^ 2 / (P.μ * P.ϕ) →
        restProfit σ fee p = p * (P.μ - P.c / (P.R - p))) ∧
      (P.R - P.c ^ 2 / (P.μ * P.ϕ) < p ∧ p ≤ P.R - P.ϕ / P.μ →
        restProfit σ fee p = p * (P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p))))) := by
  have hm : 0 < P.μ - P.Λ1 := by linarith [hP.Λ1_lt_μ]
  have hμ := hP.μ_pos
  have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  have hΛ := hP.Λ1_pos
  have hA' : P.Λ1 ≤ (P.c - P.ϕ) / P.c * P.μ → P.μ * P.ϕ ≤ P.c * (P.μ - P.Λ1) := by
    intro h
    have : P.Λ1 * P.c ≤ (P.c - P.ϕ) * P.μ := by
      have := mul_le_mul_of_nonneg_right h hc.le
      rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hc.ne'] at this
    linarith
  have hB' : (P.c - P.ϕ) / P.c * P.μ < P.Λ1 → P.c * (P.μ - P.Λ1) < P.μ * P.ϕ := by
    intro h
    have : (P.c - P.ϕ) * P.μ < P.Λ1 * P.c := by
      have := mul_lt_mul_of_pos_right h hc
      rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hc.ne'] at this
    linarith
  have tA1 : P.μ * P.ϕ ≤ P.c * (P.μ - P.Λ1) →
      P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 ≤ P.c / (P.μ - P.Λ1) := by
    intro h; rw [div_le_div_iff₀ (by positivity) hm]; nlinarith
  have tA2 : P.μ * P.ϕ ≤ P.c * (P.μ - P.Λ1) →
      P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 ≤ P.c ^ 2 / (P.μ * P.ϕ) := by
    intro h; rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ P.μ * P.ϕ := by positivity
    nlinarith [mul_le_mul h h h0 (by positivity)]
  have tB1 : P.c * (P.μ - P.Λ1) < P.μ * P.ϕ →
      P.c ^ 2 / (P.μ * P.ϕ) < P.c / (P.μ - P.Λ1) := by
    intro h; rw [div_lt_div_iff₀ (by positivity) hm]; nlinarith
  have tB2 : P.c * (P.μ - P.Λ1) < P.μ * P.ϕ →
      P.c ^ 2 / (P.μ * P.ϕ) < P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 := by
    intro h; rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 < P.c * (P.μ - P.Λ1) := by positivity
    nlinarith [mul_lt_mul'' h h h0.le h0.le]
  have hσp : ∀ p, 0 ≤ p → ∀ θ : ℝ, 0 ≤ θ → IsCustEq P p θ (σ p θ) :=
    fun p hp θ hθ => hσ p θ hp hθ
  have hrest : ∀ p, restProfit σ fee p = p * ((σ p (fee p)).lamD + (σ p (fee p)).lamW) :=
    fun p => rfl
  -- region 1
  have C1 : ∀ p, 0 ≤ p → p ≤ P.R - P.c / (P.μ - P.Λ1) →
      restProfit σ fee p = p * (P.μ - P.c / (P.R - p)) := by
    intro p hp h
    have R := g81_R1 P hP hϕ σ p (hσp p hp) h
    have hf := g81_uniq R.1 (hfee p hp) (fun hne => by
      rw [R.2.1]; exact g81_B1s P hP hϕ (hσp p hp _ (hfee p hp).1) (hfee p hp).1 h hne)
    rw [hrest, hf, R.2.1, R.2.2.1]; ring
  -- region 3
  have C3 : ∀ p, 0 ≤ p → P.ϕ / P.μ ≤ P.R - p → P.R - p < P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 →
      P.R - p ≤ P.c ^ 2 / (P.μ * P.ϕ) → P.R - p < P.c / (P.μ - P.Λ1) →
      restProfit σ fee p = p * (P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p))) := by
    intro p hp h1 h2 h3 h4
    rcases eq_or_lt_of_le h1 with heq | hlt
    · have := g81_zero P hP hϕ (hσp p hp _ (hfee p hp).1) (hfee p hp).1 heq.symm
      have hs : Real.sqrt (P.μ * P.ϕ / (P.R - p)) = P.μ := by
        rw [← heq, show P.μ * P.ϕ / (P.ϕ / P.μ) = P.μ ^ 2 by field_simp]
        exact Real.sqrt_sq hμ.le
      rw [restProfit, this, hs]; ring
    · have R := g81_R3 P hP hϕ σ p (hσp p hp) h1 h2 h3 h4
      have hf := g81_uniq R.1 (hfee p hp) (fun hne => by
        have := R.2.2.2; simp only [platProfit] at this; rw [this]
        exact g81_B3s P hP hϕ (hσp p hp _ (hfee p hp).1) (hfee p hp).1 hlt hne)
      rw [hrest, hf, R.2.1, R.2.2.1]; ring
  refine ⟨fun hA p hp => ⟨C1 p hp, fun h => ?_, fun h => ?_⟩, fun hB p hp => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have R := g81_R2A P hP hϕ σ p (hσp p hp) h.1 h.2
    have hf := g81_uniq R.1 (hfee p hp) (fun hne => by
      rw [R.2.1]; exact g81_B2As P hP hϕ (hσp p hp _ (hfee p hp).1) (hfee p hp).1 h.2 hne)
    rw [hrest, hf, R.2.1, R.2.2.1]; ring
  · exact C3 p hp (by linarith) (by linarith) (by linarith [tA2 (hA' hA)]) (by linarith [tA1 (hA' hA)])
  · by_cases h1 : p ≤ P.R - P.c / (P.μ - P.Λ1)
    · exact C1 p hp h1
    push Not at h1
    have R := g81_R2B P hP hϕ σ p (hσp p hp) h1 h
    have hf := g81_uniq R.1 (hfee p hp) (fun hne => by
      have := R.2.2.2; simp only [platProfit] at this; rw [this]
      exact g81_B2Bs P hP hϕ (hσp p hp _ (hfee p hp).1) (hfee p hp).1 h1 h hne)
    rw [hrest, hf, R.2.1, R.2.2.1]; ring
  · exact C3 p hp (by linarith) (by linarith [tB2 (hB' hB)]) (by linarith) (by linarith [tB1 (hB' hB)])
