-- Prove2me | solution 1 for FoodDeliv.Decentral.cor_C_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:37:45.483651+00:00
-- url     : https://prove2.me/submissions/acaea6d4-407f-40ca-93ed-9fd24b02eb2c

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_6
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_7
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_8

-- ==== module C2 ====
section C2

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
      linear_combination (-1 : ℝ) * this
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
      rw [this]; linarith [mul_le_mul_of_nonneg_right (show m ≤ P.μ by linarith) hϕ.le, hrm]
    rw [mul_comm r] at this; exact le_of_mul_le_mul_left this (by positivity)
  rcases eq_or_lt_of_le hs.lamD_nonneg with h0 | hD
  · rw [← h0, mul_zero]; exact mul_nonneg (by linarith) hΛ.le
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
              rw [mul_assoc, hx1m]; linarith [hrm]
            exact le_of_mul_le_mul_right this hm
          linarith [mul_lt_mul_of_pos_left hxlt hμ]
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
        linarith [mul_lt_mul_of_pos_left this hr]
      exact (pow_lt_pow_iff_left₀ hxs0.le hr.le two_ne_zero).1 this
    have hθpos : 0 < r - xs := by linarith
    have hx1 : xs < P.ϕ / (P.μ - P.Λ1) := by
      have h0 : 0 < P.ϕ / (P.μ - P.Λ1) := div_pos hϕ hm
      refine (pow_lt_pow_iff_left₀ hxs0.le h0.le two_ne_zero).1 ?_
      rw [hxs2, div_pow, div_lt_div_iff₀ hμ (by positivity)]
      have h1 : r * (P.μ - P.Λ1) ^ 2 < P.μ * P.ϕ := by
        rwa [lt_div_iff₀ (by positivity)] at hr2
      have h2 := mul_lt_mul_of_pos_left h1 hϕ
      linarith [h2]
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


end C2
-- ==== module Alg ====

namespace X5FD
open FoodDeliv.Decentral

/-- `g x = R x³ / (μ (2μ - x))` is strictly increasing on `[0, μ]`. -/
theorem g_lt {R μ x y : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ μ) :
    R * x ^ 3 / (μ * (2 * μ - x)) < R * y ^ 3 / (μ * (2 * μ - y)) := by
  have h1 : 0 < μ * (2 * μ - x) := by nlinarith
  have h2 : 0 < μ * (2 * μ - y) := by nlinarith
  rw [div_lt_div_iff₀ h1 h2]
  have hx3 : x ^ 3 < y ^ 3 := by
    exact pow_lt_pow_left₀ hxy hx (by norm_num)
  have hx3' : 0 ≤ x ^ 3 := by positivity
  have : x ^ 3 * (2 * μ - y) < y ^ 3 * (2 * μ - x) := by nlinarith
  have hRμ : 0 < R * μ := mul_pos hR hμ
  nlinarith

theorem g_le_iff {R μ x y : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hx : 0 ≤ x) (hx' : x ≤ μ)
    (hy : 0 ≤ y) (hy' : y ≤ μ) :
    R * x ^ 3 / (μ * (2 * μ - x)) ≤ R * y ^ 3 / (μ * (2 * μ - y)) ↔ x ≤ y := by
  constructor
  · intro h; by_contra h'; push Not at h'
    exact absurd h (not_le.mpr (g_lt hR hμ hy h' hx'))
  · intro h; rcases h.lt_or_eq with h | h
    · exact (g_lt hR hμ hx h hy').le
    · rw [h]

/-- `f x = 2R(μ-x)²/(2μ-x)` is strictly decreasing on `[0, μ]`. -/
theorem f_lt {R μ x y : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ μ) :
    2 * R * (μ - y) ^ 2 / (2 * μ - y) < 2 * R * (μ - x) ^ 2 / (2 * μ - x) := by
  have h1 : 0 < 2 * μ - x := by linarith
  have h2 : 0 < 2 * μ - y := by linarith
  rw [div_lt_div_iff₀ h2 h1]
  have key : (μ - y) ^ 2 * (2 * μ - x) < (μ - x) ^ 2 * (2 * μ - y) := by
    have ha : μ - y < μ - x := by linarith
    have hb : 0 ≤ μ - y := by linarith
    have : (μ - x) ^ 2 * (2 * μ - y) - (μ - y) ^ 2 * (2 * μ - x)
        = ((μ - x) - (μ - y)) * (μ * ((μ - x) + (μ - y)) + (μ - x) * (μ - y)) := by ring
    have : 0 < ((μ - x) - (μ - y)) * (μ * ((μ - x) + (μ - y)) + (μ - x) * (μ - y)) := by
      apply mul_pos (by linarith); nlinarith
    linarith
  nlinarith

theorem f_le_iff {R μ x y : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hx : 0 ≤ x) (hx' : x ≤ μ)
    (hy : 0 ≤ y) (hy' : y ≤ μ) :
    2 * R * (μ - y) ^ 2 / (2 * μ - y) ≤ 2 * R * (μ - x) ^ 2 / (2 * μ - x) ↔ x ≤ y := by
  constructor
  · intro h; by_contra h'; push Not at h'
    exact absurd h (not_le.mpr (f_lt hR hμ hy h' hx'))
  · intro h; rcases h.lt_or_eq with h | h
    · exact (f_lt hR hμ hx h hy').le
    · rw [h]

theorem sqrt_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : y ^ 2 = x) : Real.sqrt x = y := by
  rw [← h]; exact Real.sqrt_sq hy

section
variable {R μ c : ℝ} (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
include hμ hc hcR

theorem R_pos : 0 < R := by
  by_contra h; push Not at h; nlinarith

/-- `χ1` lies in `(0, μ)` and `f χ1 = (√(Rμ) - √c)²`. -/
theorem chi1_spec :
    0 < chi1 R μ c ∧ chi1 R μ c < μ ∧
      2 * R * (μ - chi1 R μ c) ^ 2 / (2 * μ - chi1 R μ c) = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 := by
  have hR := R_pos hμ hc hcR
  set s := Real.sqrt (R * μ) with hs
  set t := Real.sqrt c with ht
  have hs2 : s ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = c := Real.sq_sqrt hc.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hc
  have hst : t < s := Real.sqrt_lt_sqrt hc.le hcR
  have hRcμ : Real.sqrt (R * c * μ) = s * t := by
    rw [hs, ht, ← Real.sqrt_mul (by positivity)]; congr 1; ring
  unfold chi1
  rw [hRcμ]
  set d := c - 2 * (s * t) with hd
  set B := 3 * R * μ - d with hB
  set Δ := B ^ 2 + 16 * R * μ * d with hΔ
  have hd0 : d < 0 := by rw [hd, ← ht2]; nlinarith
  have hK : 0 < (s - t) ^ 2 := by nlinarith
  -- q(μ) = -μ K
  have hΔpos : (4 * R * μ - B) ^ 2 < Δ := by
    rw [hΔ, hB, hd, ← ht2]; nlinarith [hs2]
  have hΔ0 : 0 ≤ Δ := le_trans (sq_nonneg _) hΔpos.le
  have hsq := Real.sq_sqrt hΔ0
  have hsq0 := Real.sqrt_nonneg Δ
  have hB0 : 0 < B := by rw [hB]; nlinarith
  have hBΔ : Δ < B ^ 2 := by rw [hΔ]; nlinarith
  have h1 : Real.sqrt Δ < B := by
    rw [← Real.sqrt_sq hB0.le]; exact Real.sqrt_lt_sqrt hΔ0 hBΔ
  have h2 : B - Real.sqrt Δ < 4 * R * μ := by
    have := Real.sqrt_lt_sqrt (sq_nonneg _) hΔpos
    rw [Real.sqrt_sq_eq_abs] at this
    have := le_abs_self (4 * R * μ - B)
    have := neg_abs_le (4 * R * μ - B)
    linarith
  refine ⟨by apply div_pos (by linarith) (by positivity), ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · set x := (B - Real.sqrt Δ) / (4 * R) with hx
    have hx4 : 4 * R * x = B - Real.sqrt Δ := by rw [hx]; field_simp
    have hxμ : x < μ := by rw [hx, div_lt_iff₀ (by positivity)]; linarith
    have hq : 2 * R * x ^ 2 - B * x - 2 * μ * d = 0 := by
      have : 8 * R * (2 * R * x ^ 2 - B * x - 2 * μ * d) = (4 * R * x - B) ^ 2 - B ^ 2 - 16 * R * μ * d := by ring
      have h' : (4 * R * x - B) ^ 2 = Δ := by rw [hx4]; nlinarith
      have : 8 * R * (2 * R * x ^ 2 - B * x - 2 * μ * d) = 0 := by rw [this, h', hΔ]; ring
      have h8 : (8 * R) ≠ 0 := by positivity
      exact (mul_eq_zero.mp this).resolve_left h8
    rw [div_eq_iff (by linarith)]
    rw [hB, hd, ← ht2] at hq
    have : (s - t) ^ 2 = R * μ + t ^ 2 - 2 * (s * t) := by nlinarith
    rw [this]; linear_combination hq

end
end X5FD

-- ==== module Main ====

namespace X5FD
open FoodDeliv.Decentral

noncomputable def Acurve (R μ c p : ℝ) : ℝ := p * (μ - c / (R - p))
noncomputable def Dcurve (R μ ϕ p : ℝ) : ℝ := p * (μ - Real.sqrt (μ * ϕ / (R - p)))

theorem zero_region (P : Params) (hP : P.Standing) (p θ : ℝ) (s : Profile)
    (hs : IsCustEq P p θ s) (hθ : 0 ≤ θ) (hp : P.R - P.ϕ / P.μ < p) : s.total = 0 := by
  have htot : 0 ≤ s.total := by
    unfold Profile.total Profile.lamW; linarith [hs.lamD_nonneg, hs.lam1W_nonneg, hs.lam0W_nonneg]
  have hlt := hs.total_lt
  have hpos : 0 < P.μ - s.total := by linarith
  have hϕμ : P.ϕ / P.μ ≤ P.ϕ / (P.μ - s.total) :=
    div_le_div_of_nonneg_left hP.ϕ_nonneg hpos (by linarith)
  have hcμ : P.c / P.μ ≤ P.c / (P.μ - s.total) :=
    div_le_div_of_nonneg_left hP.c_pos.le hpos (by linarith)
  have hϕc : P.ϕ / P.μ < P.c / P.μ := div_lt_div_of_pos_right hP.ϕ_lt_c hP.μ_pos
  have hD : s.lamD = 0 := by
    by_contra h
    have := (hs.tech_deliv (lt_of_le_of_ne hs.lamD_nonneg (Ne.symm h))).1
    unfold UD at this; linarith
  have hW : 0 ≤ UW P p s.total → False := by intro h; unfold UW at h; linarith
  have h1 : s.lam1W = 0 := by
    by_contra h; exact hW (hs.tech_walk (lt_of_le_of_ne hs.lam1W_nonneg (Ne.symm h))).1
  have h0 : s.lam0W = 0 := by
    by_contra h; exact hW (hs.trad_join (lt_of_le_of_ne hs.lam0W_nonneg (Ne.symm h)))
  unfold Profile.total Profile.lamW; rw [hD, h1, h0]; ring

theorem fin_step (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ) (V pT : ℝ) (hpT : 0 < pT)
    (hle : ∀ p, 0 ≤ p → restProfit σ fee p ≤ V) (heq : restProfit σ fee pT = V) :
    IsOptPrice σ fee pT ∧ restProfit σ fee pT = V ∧ (σ pT (fee pT)).total = V / pT := by
  refine ⟨⟨hpT.le, fun p hp => heq ▸ hle p hp⟩, heq, ?_⟩
  rw [← heq]; unfold restProfit; field_simp

/-- The curve facts collected from Lemmas C.6–C.8 plus algebra. -/
theorem facts (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    let K := (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
    let χ := chi R μ ϕ
    let M := 2 * R * (μ - χ) ^ 2 / (2 * μ - χ)
    let pA := R - Real.sqrt (c / μ * R)
    let pD := 2 * R * (μ - χ) / (2 * μ - χ)
    let pc := R - c ^ 2 / (μ * ϕ)
    -- walk-in curve
    (∀ p, 0 ≤ p → p ≤ R - ϕ / μ → Acurve R μ c p ≤ K) ∧
    (0 < pA ∧ pA ≤ R - ϕ / μ ∧ Acurve R μ c pA = K) ∧
    -- delivery curve
    (∀ p, 0 ≤ p → p ≤ R - ϕ / μ → Dcurve R μ ϕ p ≤ M) ∧
    (0 < pD ∧ pD ≤ R - ϕ / μ ∧ Dcurve R μ ϕ pD = M) ∧
    (∀ p q, pD ≤ p → p < q → q ≤ R - ϕ / μ → Dcurve R μ ϕ q < Dcurve R μ ϕ p) ∧
    -- comparisons
    (∀ p, 0 < p → p < R → p ≤ pc → Dcurve R μ ϕ p ≤ Acurve R μ c p) ∧
    (∀ p, 0 < p → p < R → pc < p → Acurve R μ c p < Dcurve R μ ϕ p) ∧
    (∀ p, 0 < p → p < pc → Dcurve R μ ϕ p < Acurve R μ c p) ∧
    -- chi and the delivery-only curve
    (0 < χ ∧ χ < μ ∧ ϕ * (μ * (2 * μ - χ)) = R * χ ^ 3) ∧
    pD = R - μ * ϕ / χ ^ 2 ∧
    (∀ l ∈ Set.Ioo 0 μ, Dcurve R μ ϕ (R - μ * ϕ / (μ - l) ^ 2) = deliveryCurve R μ ϕ l) ∧
    (∀ l ∈ Set.Ioo 0 μ, deliveryCurve R μ ϕ l ≤ M) ∧
    deliveryCurve R μ ϕ (lam2 R μ ϕ) = M ∧
    StrictMonoOn (fun l => deliveryCurve R μ ϕ l) (Set.Ioc 0 (lam2 R μ ϕ)) ∧
    StrictAntiOn (fun l => deliveryCurve R μ ϕ l) (Set.Ico (lam2 R μ ϕ) μ) ∧
    (∀ l ∈ Set.Ioo 0 μ, (l ≤ (c - ϕ) / c * μ ↔ R - c / (μ - l) ≤ R - μ * ϕ / (μ - l) ^ 2)) ∧
    -- K ≤ M consequences
    (K ≤ M → lam2 R μ ϕ ≤ (c - ϕ) / c * μ ∧ 0 < lam1 R μ c ϕ ∧ lam1 R μ c ϕ ≤ lam2 R μ ϕ ∧
      deliveryCurve R μ ϕ (lam1 R μ c ϕ) = K ∧ pA < pD) ∧
    (ϕ ≤ phi1 R μ c ↔ K ≤ M) := by
  intro K χ M pA pD pc
  have hR := R_pos hμ hc hcR
  obtain ⟨-, ⟨mA, hmA, hAmono, hAanti⟩, hAgr, hAset, -, -⟩ := lemma_C_6 R μ c ϕ hμ hc hcR hϕ hϕc
  obtain ⟨-, ⟨hχmem, hχcub, -⟩, ⟨mD, hmD, hDmono, hDanti⟩, hDgr, hDset, -, -, hC74⟩ :=
    lemma_C_7 R μ c ϕ hμ hc hcR hϕ hϕc
  obtain ⟨⟨-, -, hAD⟩, hDpb, ⟨hl2mem, hdcmono, hdcanti, hdcl2, hdcgr⟩, hl1, -, hlc, -, hbar2⟩ :=
    lemma_C_8 R μ c ϕ hμ hc hcR hϕ hϕc
  -- walk-in curve
  have hA_le : ∀ p, 0 ≤ p → p ≤ R - ϕ / μ → Acurve R μ c p ≤ K := by
    intro p hp0 hp1
    rcases hp0.lt_or_eq with hp0 | hp0
    · exact hAgr.2 ⟨p, ⟨hp0, hp1⟩, rfl⟩
    · subst hp0; simp only [Acurve, zero_mul]; positivity
  have hpAmem : pA ∈ {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - c / (R - q)) ≤ p * (μ - c / (R - p))} := by
    rw [hAset]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨⟨hpA0, hpA1⟩, hpAmax⟩ := hpAmem
  obtain ⟨q, hq, hqK⟩ := hAgr.1
  have hApA : Acurve R μ c pA = K := by
    apply le_antisymm (hAgr.2 ⟨pA, ⟨hpA0, hpA1⟩, rfl⟩)
    have h := hpAmax q hq; simp only at hqK; rw [hqK] at h; exact h
  -- delivery curve
  have hD_le : ∀ p, 0 ≤ p → p ≤ R - ϕ / μ → Dcurve R μ ϕ p ≤ M := by
    intro p hp0 hp1
    rcases hp0.lt_or_eq with hp0 | hp0
    · exact hDgr.2 ⟨p, ⟨hp0, hp1⟩, rfl⟩
    · subst hp0; simp only [Dcurve, zero_mul]
      have : χ ≤ μ := hχmem.2
      have : 0 ≤ μ - χ := by linarith
      have : 0 < 2 * μ - χ := by linarith
      positivity
  have hpDmem : pD ∈ {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - Real.sqrt (μ * ϕ / (R - q))) ≤ p * (μ - Real.sqrt (μ * ϕ / (R - p)))} := by
    rw [hDset]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨⟨hpD0, hpD1⟩, hpDmax⟩ := hpDmem
  obtain ⟨q', hq', hqM⟩ := hDgr.1
  have hDpD : Dcurve R μ ϕ pD = M := by
    apply le_antisymm (hDgr.2 ⟨pD, ⟨hpD0, hpD1⟩, rfl⟩)
    have h := hpDmax q' hq'; simp only at hqM; rw [hqM] at h; exact h
  have hmDmax : ∀ q ∈ Set.Ioc 0 (R - ϕ / μ), Dcurve R μ ϕ q ≤ Dcurve R μ ϕ mD := by
    intro q hq
    rcases le_or_gt q mD with h | h
    · exact hDmono.monotoneOn ⟨hq.1, h⟩ ⟨hmD.1, le_rfl⟩ h
    · exact hDanti.antitoneOn ⟨le_rfl, hmD.2⟩ ⟨h.le, hq.2⟩ h.le
  have hmDeq : mD = pD := by
    have : mD ∈ {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - Real.sqrt (μ * ϕ / (R - q))) ≤ p * (μ - Real.sqrt (μ * ϕ / (R - p)))} :=
      ⟨hmD, hmDmax⟩
    rw [hDset] at this; exact this
  have hD_anti : ∀ p q, pD ≤ p → p < q → q ≤ R - ϕ / μ → Dcurve R μ ϕ q < Dcurve R μ ϕ p := by
    intro p q hp hpq hq
    rw [← hmDeq] at hp
    exact hDanti ⟨hp, by linarith⟩ ⟨by linarith, hq⟩ hpq
  -- strict comparison below pc
  have hstrict : ∀ p, 0 < p → p < pc → Dcurve R μ ϕ p < Acurve R μ c p := by
    intro p hp hpc
    have hpos : c ^ 2 / (μ * ϕ) < R - p := by simp only [pc] at hpc; linarith
    have hc2 : 0 < c ^ 2 / (μ * ϕ) := by positivity
    have hRp : 0 < R - p := by linarith
    unfold Dcurve Acurve
    apply mul_lt_mul_of_pos_left _ hp
    have : c / (R - p) < Real.sqrt (μ * ϕ / (R - p)) := by
      rw [Real.lt_sqrt (by positivity)]
      rw [div_lt_iff₀ (mul_pos hμ hϕ)] at hpos
      rw [div_pow, div_lt_div_iff₀ (by positivity) hRp]
      nlinarith
    linarith
  -- chi
  have hl2 : lam2 R μ ϕ = μ - χ := rfl
  have hχ0 : 0 < χ := by have := hl2mem.2; rw [hl2] at this; linarith
  have hχμ : χ < μ := by have := hl2mem.1; rw [hl2] at this; linarith
  have hcub' : ϕ * (μ * (2 * μ - χ)) = R * χ ^ 3 := by
    unfold chiCubic at hχcub; linear_combination hχcub
  have h2χ : 2 * μ - χ ≠ 0 := by linarith
  have hpDeq : pD = R - μ * ϕ / χ ^ 2 := by
    have : μ * ϕ / χ ^ 2 = R * χ / (2 * μ - χ) := by
      rw [div_eq_div_iff (by positivity) h2χ]; linear_combination hcub'
    rw [this]; simp only [pD]; field_simp; ring
  -- K ≤ M consequences
  have hKMc : K ≤ M → lam2 R μ ϕ ≤ (c - ϕ) / c * μ ∧ 0 < lam1 R μ c ϕ ∧
      lam1 R μ c ϕ ≤ lam2 R μ ϕ ∧ deliveryCurve R μ ϕ (lam1 R μ c ϕ) = K ∧ pA < pD := by
    intro hKM
    have hpcD : pc ≤ pD := by
      by_contra h; push Not at h
      have := hstrict pD hpD0 h
      rw [hDpD] at this; linarith [hA_le pD hpD0.le hpD1]
    have hl2c : lam2 R μ ϕ ≤ (c - ϕ) / c * μ := by
      rw [hpDeq] at hpcD
      have h1 : μ * ϕ / χ ^ 2 ≤ c ^ 2 / (μ * ϕ) := by simp only [pc] at hpcD; linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1
      have h2 : μ * ϕ ≤ c * χ := by nlinarith [mul_nonneg hc.le hχ0.le, mul_pos hμ hϕ]
      rw [hl2, show (c - ϕ) / c * μ = μ - μ * ϕ / c by field_simp]
      have : μ * ϕ / c ≤ χ := by rw [div_le_iff₀ hc]; linarith
      linarith
    have hpApD : pA < pD := by
      have : ¬ ((Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) < ϕ) := by
        intro h; have := hbar2 h; linarith
      exact hC74 (not_lt.mp this)
    rcases hKM.lt_or_eq with hlt | heq
    · obtain ⟨⟨l', -, hS⟩, hl12⟩ := hl1 hlt
      have hmem : lam1 R μ c ϕ ∈ {l : ℝ | l ∈ Set.Ioo 0 μ ∧
          deliveryCurve R μ ϕ l = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2} := by
        rw [hS]; exact Or.inl rfl
      exact ⟨hl2c, hmem.1.1, hl12.le, hmem.2, hpApD⟩
    · have hS : {l : ℝ | l ∈ Set.Ioo 0 μ ∧
          deliveryCurve R μ ϕ l = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2} = {lam2 R μ ϕ} := by
        ext l; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor
        · rintro ⟨hl, hdl⟩
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := hdcmono ⟨hl.1, h.le⟩ ⟨hl2mem.1, le_rfl⟩ h
            simp only at this; rw [hdl, hdcl2] at this; linarith
          · have := hdcanti ⟨le_rfl, hl2mem.2⟩ ⟨h.le, hl.2⟩ h
            simp only at this; rw [hdl, hdcl2] at this; linarith
        · rintro rfl; exact ⟨hl2mem, by rw [hdcl2]; exact heq.symm⟩
      have h12 : lam1 R μ c ϕ = lam2 R μ ϕ := by unfold lam1; rw [hS, csInf_singleton]
      refine ⟨hl2c, h12 ▸ hl2mem.1, h12.le, ?_, hpApD⟩
      rw [h12, hdcl2]; exact heq.symm
  -- ϕ ≤ ϕ1 ↔ K ≤ M
  have hiff : ϕ ≤ phi1 R μ c ↔ K ≤ M := by
    obtain ⟨h10, h1μ, hf1⟩ := chi1_spec hμ hc hcR
    have hϕeq : ϕ = R * χ ^ 3 / (μ * (2 * μ - χ)) := by
      rw [eq_div_iff (by positivity)]; exact hcub'
    have e1 : (ϕ ≤ phi1 R μ c) ↔ (R * χ ^ 3 / (μ * (2 * μ - χ)) ≤
        R * chi1 R μ c ^ 3 / (μ * (2 * μ - chi1 R μ c))) := by
      rw [← hϕeq]; rfl
    rw [e1, g_le_iff hR hμ hχ0.le hχμ.le h10.le h1μ.le,
      ← f_le_iff hR hμ hχ0.le hχμ.le h10.le h1μ.le, hf1]
  exact ⟨hA_le, ⟨hpA0, hpA1, hApA⟩, hD_le, ⟨hpD0, hpD1, hDpD⟩, hD_anti,
    fun p hp hpR h => (hAD p hp hpR).1 h, fun p hp hpR h => (hAD p hp hpR).2 h, hstrict,
    ⟨hχ0, hχμ, hcub'⟩, hpDeq, fun l hl => hDpb l hl, fun l hl => hdcgr.2 ⟨l, hl, rfl⟩, hdcl2,
    hdcmono, hdcanti, fun l hl => (hlc l hl).1, hKMc, hiff⟩

end X5FD

-- ==== module C3 ====

namespace X5FD
open FoodDeliv.Decentral Filter Topology

/-! Best-response fee at a given price, one lemma per price region (from the cor_C_2 lemmas). -/

theorem U1 {R μ c ϕ Λ0 Λ1 p : ℝ} (hP : Params.Standing ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (hϕ : 0 < ϕ)
    {σ : ℝ → ℝ → Profile} {fee : ℝ → ℝ}
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hf : IsFeeBR σ p (fee p)) (hp : p ≤ R - c / (μ - Λ1)) :
    fee p = (c - ϕ) * (R - p) / c ∧ (σ p (fee p)).lamD = Λ1 ∧
      (σ p (fee p)).lamW = μ - c / (R - p) - Λ1 := by
  have h := g81_R1 _ hP hϕ σ p hσ hp
  have e := g81_uniq h.1 hf (fun hne => by
    rw [h.2.1]; exact g81_B1s _ hP hϕ (hσ _ hf.1) hf.1 hp hne)
  rw [e]; exact ⟨rfl, h.2.1, h.2.2.1⟩

theorem U2A {R μ c ϕ Λ0 Λ1 p : ℝ} (hP : Params.Standing ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (hϕ : 0 < ϕ)
    {σ : ℝ → ℝ → Profile} {fee : ℝ → ℝ}
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hf : IsFeeBR σ p (fee p)) (hp1 : R - c / (μ - Λ1) < p)
    (hp : p ≤ R - μ * ϕ / (μ - Λ1) ^ 2) :
    fee p = R - p - ϕ / (μ - Λ1) ∧ (σ p (fee p)).lamD = Λ1 ∧ (σ p (fee p)).lamW = 0 := by
  have h := g81_R2A _ hP hϕ σ p hσ hp1 hp
  have e := g81_uniq h.1 hf (fun hne => by
    rw [h.2.1]; exact g81_B2As _ hP hϕ (hσ _ hf.1) hf.1 hp hne)
  rw [e]; exact ⟨rfl, h.2.1, h.2.2.1⟩

theorem U2B {R μ c ϕ Λ0 Λ1 p : ℝ} (hP : Params.Standing ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (hϕ : 0 < ϕ)
    {σ : ℝ → ℝ → Profile} {fee : ℝ → ℝ}
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hf : IsFeeBR σ p (fee p)) (hp1 : R - c / (μ - Λ1) < p)
    (hp : p ≤ R - c ^ 2 / (μ * ϕ)) :
    fee p = (c - ϕ) * (R - p) / c ∧ (σ p (fee p)).lamD = μ - c / (R - p) ∧
      (σ p (fee p)).lamW = 0 := by
  have h := g81_R2B _ hP hϕ σ p hσ hp1 hp
  have e := g81_uniq h.1 hf (fun hne => by
    have := h.2.2.2; simp only [platProfit] at this; rw [this]
    exact g81_B2Bs _ hP hϕ (hσ _ hf.1) hf.1 hp1 hp hne)
  rw [e]; exact ⟨rfl, h.2.1, h.2.2.1⟩

theorem U3 {R μ c ϕ Λ0 Λ1 p : ℝ} (hP : Params.Standing ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (hϕ : 0 < ϕ)
    {σ : ℝ → ℝ → Profile} {fee : ℝ → ℝ}
    (hσ : ∀ θ : ℝ, 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hf : IsFeeBR σ p (fee p)) (hr1 : ϕ / μ < R - p) (hr2 : R - p < μ * ϕ / (μ - Λ1) ^ 2)
    (hr3 : R - p ≤ c ^ 2 / (μ * ϕ)) (hr4 : R - p < c / (μ - Λ1)) :
    fee p = R - p - Real.sqrt (μ * ϕ * (R - p)) / μ ∧
      (σ p (fee p)).lamD = μ - Real.sqrt (μ * ϕ / (R - p)) ∧ (σ p (fee p)).lamW = 0 := by
  have h := g81_R3 _ hP hϕ σ p hσ hr1.le hr2 hr3 hr4
  have e := g81_uniq h.1 hf (fun hne => by
    have := h.2.2.2; simp only [platProfit] at this; rw [this]
    exact g81_B3s _ hP hϕ (hσ _ hf.1) hf.1 hr1 hne)
  rw [e]; exact ⟨rfl, h.2.1, h.2.2.1⟩

/-! The table of Corollary C.3. -/

noncomputable def pT3 (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then R - Real.sqrt (c / μ * R)
          else if Λ1 ≤ lam2 R μ ϕ then R - μ * ϕ / (μ - Λ1) ^ 2
          else 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ))
      else R - Real.sqrt (c / μ * R)

noncomputable def θT3 (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then (c - ϕ) * Real.sqrt (R / (μ * c))
          else if Λ1 ≤ lam2 R μ ϕ then ϕ * Λ1 / (μ - Λ1) ^ 2
          else R * chi R μ ϕ * (μ - chi R μ ϕ) / (μ * (2 * μ - chi R μ ϕ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then (c - ϕ) * Real.sqrt (R / (c * μ))
          else (c - ϕ) * Real.sqrt (R / (c * μ)))

noncomputable def πT3 (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else if Λ1 ≤ lam2 R μ ϕ then ϕ * Λ1 ^ 2 / (μ - Λ1) ^ 2
          else R * chi R μ ϕ * (μ - chi R μ ϕ) ^ 2 / (μ * (2 * μ - chi R μ ϕ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else (c - ϕ) * (Real.sqrt (R * μ / c) - 1))

noncomputable def DT3 (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then Λ1 else if Λ1 ≤ lam2 R μ ϕ then Λ1 else μ - chi R μ ϕ)
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then Λ1 else μ - Real.sqrt (c * μ / R))

noncomputable def WT3 (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then μ - Real.sqrt (c * μ / R) - Λ1
          else if Λ1 ≤ lam2 R μ ϕ then 0 else 0)
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then μ - Real.sqrt (c * μ / R) - Λ1 else 0)

/-- Square-root bookkeeping with `s = √(Rμ)`, `t = √c`. -/
theorem sq_facts {R μ c : ℝ} (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ) :
    let s := Real.sqrt (R * μ)
    let t := Real.sqrt c
    s ^ 2 = R * μ ∧ t ^ 2 = c ∧ 0 < s ∧ 0 < t ∧ t < s ∧
    Real.sqrt (c / μ * R) = R * t / s ∧ Real.sqrt (c * μ / R) = μ * t / s ∧
    Real.sqrt (R / (c * μ)) = s / (μ * t) ∧ Real.sqrt (R / (μ * c)) = s / (μ * t) ∧
    Real.sqrt (R * μ / c) = s / t := by
  intro s t
  have hR := R_pos hμ hc hcR
  have hs2 : s ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = c := Real.sq_sqrt hc.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hc
  have hst : t < s := Real.sqrt_lt_sqrt hc.le hcR
  have hR' : R = s ^ 2 / μ := by rw [hs2]; field_simp
  refine ⟨hs2, ht2, hs0, ht0, hst, ?_, ?_, ?_, ?_, ?_⟩
  · apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  · apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  · apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  · apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  · apply sqrt_of_sq (by positivity)
    rw [div_pow, ht2, hs2]

/-- Under `K ≤ M`, `λ1 < μ - √(cμ/R)`. -/
theorem lam1_lt_lamA (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hKM : ϕ ≤ phi1 R μ c) :
    lam1 R μ c ϕ < μ - Real.sqrt (c * μ / R) := by
  have hR := R_pos hμ hc hcR
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hχ0, hχμ, hcub⟩, -, -, -, -, hdcmono, -, -, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  obtain ⟨-, hL10, hL12, hdcL1, -⟩ := hKMc (hiff.1 hKM)
  obtain ⟨hs2, ht2, hs0, ht0, hst, -, hsqT, -, -, -⟩ := sq_facts hμ hc hcR
  set s := Real.sqrt (R * μ)
  set t := Real.sqrt c
  rw [hsqT]
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set χ := chi R μ ϕ
  by_cases hA : μ - μ * t / s ≤ lam2 R μ ϕ
  · -- deliveryCurve at λA exceeds K
    have hm : χ ≤ μ * t / s := by rw [hl2] at hA; linarith
    have hmμ : μ * t / s ≤ μ := by
      rw [div_le_iff₀ hs0]; linarith [mul_le_mul_of_nonneg_left hst.le hμ.le]
    have hϕeq : ϕ = R * χ ^ 3 / (μ * (2 * μ - χ)) := by
      rw [eq_div_iff (mul_pos hμ (by linarith)).ne']; exact hcub
    have hg := (g_le_iff hR hμ hχ0.le hχμ.le (by positivity) hmμ).2 hm
    rw [← hϕeq] at hg
    have hgv : R * (μ * t / s) ^ 3 / (μ * (2 * μ - μ * t / s)) = t ^ 3 / (2 * s - t) := by
      have hR' : R = s ^ 2 / μ := by rw [hs2]; field_simp
      rw [hR']
      have : 2 * s - t ≠ 0 := by linarith
      field_simp
    rw [hgv] at hg
    have hϕlt : ϕ * s < t ^ 3 := by
      have h1 : ϕ * (2 * s - t) ≤ t ^ 3 := by
        rwa [le_div_iff₀ (by linarith)] at hg
      linarith [mul_pos hϕ (sub_pos.2 hst)]
    have hA0 : 0 < μ - μ * t / s := by
      have : μ * t / s < μ := by rw [div_lt_iff₀ hs0]; linarith [mul_lt_mul_of_pos_left hst hμ]
      linarith
    have hdcA : (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 < deliveryCurve R μ ϕ (μ - μ * t / s) := by
      unfold deliveryCurve
      have hR' : R = s ^ 2 / μ := by rw [hs2]; field_simp
      have e : μ - (μ - μ * t / s) = μ * t / s := by ring
      rw [e]
      have e2 : (μ - μ * t / s) * (R - μ * ϕ / (μ * t / s) ^ 2) = (s - t) * s * (t ^ 2 - ϕ) / t ^ 2 := by
        rw [hR']; field_simp
      rw [e2, lt_div_iff₀ (by positivity)]
      change (s - t) ^ 2 * t ^ 2 < (s - t) * s * (t ^ 2 - ϕ)
      have hst' : 0 < s - t := by linarith
      have : (s - t) * t ^ 2 < s * (t ^ 2 - ϕ) := by linarith [hϕlt]
      linarith [mul_lt_mul_of_pos_left this hst']
    by_contra hge; push Not at hge
    have := hdcmono.monotoneOn ⟨hA0, hA⟩ ⟨hL10, hL12⟩ hge
    rw [hdcL1] at this; linarith
  · push Not at hA; linarith

end X5FD

-- ==== module C3T ====

namespace X5FD
open FoodDeliv.Decentral Filter Topology

set_option maxHeartbeats 2000000 in
theorem tab (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0)
    (Λ1 : ℝ) (hΛ : Λ1 ∈ Set.Ioo 0 μ) (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ)
    (hσ : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hfee : ∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) :
    fee (pT3 R μ c ϕ Λ1) = θT3 R μ c ϕ Λ1 ∧
      platProfit σ (pT3 R μ c ϕ Λ1) (fee (pT3 R μ c ϕ Λ1)) = πT3 R μ c ϕ Λ1 ∧
      (σ (pT3 R μ c ϕ Λ1) (fee (pT3 R μ c ϕ Λ1))).lamD = DT3 R μ c ϕ Λ1 ∧
      (σ (pT3 R μ c ϕ Λ1) (fee (pT3 R μ c ϕ Λ1))).lamW = WT3 R μ c ϕ Λ1 := by
  have hR := R_pos hμ hc hcR
  have hP : Params.Standing ⟨R, μ, c, ϕ, Λ0, Λ1⟩ := ⟨hμ, hc, hcR, hϕ.le, hϕc, hΛ0, hΛ.1, hΛ.2⟩
  have key : ∀ p, 0 ≤ p → ∀ θ : ℝ, 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ) :=
    fun p hp θ hθ => hσ p θ hp hθ
  obtain ⟨hA_le, ⟨hpA0, hpA1, hApA⟩, hD_le, ⟨hpD0, hpD1, hDpD⟩, -, -, hAD2, hstrict,
    ⟨hχ0, hχμ, hcub⟩, hpDeq, -, -, -, hdcmono, -, hlc, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  have hy : 0 < μ - Λ1 := by linarith [hΛ.2]
  have hΛp := hΛ.1
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  have hlam1A := lam1_lt_lamA R μ c ϕ hμ hc hcR hϕ hϕc
  obtain ⟨hs2, ht2, hs0, ht0, hst, hsqA, hsqT, hk1, hk2, hk3⟩ := sq_facts hμ hc hcR
  unfold pT3 θT3 πT3 DT3 WT3 platProfit
  set s := Real.sqrt (R * μ) with hsdef
  set t := Real.sqrt c with htdef
  set χ := chi R μ ϕ with hχdef
  rw [hsqA] at hpA0 hpA1 hApA ⊢
  rw [hsqT] at hlam1A ⊢
  rw [hk1, hk2, hk3]
  have hyne : μ - Λ1 ≠ 0 := hy.ne'
  have htne : t ≠ 0 := ht0.ne'
  have hsne : s ≠ 0 := hs0.ne'
  have hR' : R = s ^ 2 / μ := by rw [hs2]; field_simp
  have hc' : c = t ^ 2 := ht2.symm
  have hAt : 0 < μ * t / s := by positivity
  -- region 1 test at pA
  have hA1 : Λ1 ≤ μ - μ * t / s → R - R * t / s ≤ R - c / (μ - Λ1) := by
    intro h
    have h1 : c / (μ - Λ1) ≤ c / (μ * t / s) := div_le_div_of_nonneg_left hc.le hAt (by linarith)
    have h2 : c / (μ * t / s) = R * t / s := by rw [hR', hc']; field_simp
    linarith
  have hA1' : μ - μ * t / s < Λ1 → R - c / (μ - Λ1) < R - R * t / s := by
    intro h
    have h1 : c / (μ * t / s) < c / (μ - Λ1) := div_lt_div_of_pos_left hc hy (by linarith)
    have h2 : c / (μ * t / s) = R * t / s := by rw [hR', hc']; field_simp
    linarith
  by_cases h1 : ϕ ≤ phi1 R μ c
  · simp only [if_pos h1]
    obtain ⟨hl2c, hL10, hL12, hdcL1, -⟩ := hKMc (hiff.1 h1)
    by_cases hA : Λ1 ≤ lam1 R μ c ϕ
    · simp only [if_pos hA]
      obtain ⟨e1, e2, e3⟩ := U1 hP hϕ (key _ hpA0.le) (hfee _ hpA0.le)
        (hA1 (by linarith [hlam1A h1]))
      rw [e2, e3, e1]
      refine ⟨?_, ?_, rfl, ?_⟩
      · rw [hR', hc']; field_simp; ring
      · rw [hR', hc']; field_simp; ring
      · have e : R - (R - R * t / s) = R * t / s := by ring
        have e2 : c / (R * t / s) = μ * t / s := by
          rw [div_eq_div_iff (by positivity) (by positivity), hR', hc']; field_simp
        rw [e, e2]
    · simp only [if_neg hA]
      push Not at hA
      by_cases hB : Λ1 ≤ lam2 R μ ϕ
      · simp only [if_pos hB]
        have hlcΛ := (hlc Λ1 hΛ).1 (le_trans hB hl2c)
        have hdc := hdcmono ⟨hL10, hL12⟩ ⟨hΛp, hB⟩ hA
        simp only at hdc
        rw [hdcL1] at hdc
        have hK0 : 0 < (s - t) ^ 2 := pow_pos (by linarith) 2
        have hpb0 : 0 < R - μ * ϕ / (μ - Λ1) ^ 2 := by
          unfold deliveryCurve at hdc
          exact pos_of_mul_pos_right (lt_trans hK0 hdc) hΛp.le
        by_cases hq : R - μ * ϕ / (μ - Λ1) ^ 2 ≤ R - c / (μ - Λ1)
        · obtain ⟨e1, e2, e3⟩ := U1 hP hϕ (key _ hpb0.le) (hfee _ hpb0.le) hq
          rw [e2, e3, e1]
          have heq : μ * ϕ / (μ - Λ1) ^ 2 = c / (μ - Λ1) := by linarith
          have heq' : μ * ϕ = c * (μ - Λ1) := by
            field_simp at heq; linarith
          have er : R - (R - μ * ϕ / (μ - Λ1) ^ 2) = c / (μ - Λ1) := by linarith
          rw [er]
          have hf : (c - ϕ) * (c / (μ - Λ1)) / c = ϕ * Λ1 / (μ - Λ1) ^ 2 := by
            rw [show ϕ * Λ1 / (μ - Λ1) ^ 2 = μ * ϕ / (μ - Λ1) ^ 2 - ϕ / (μ - Λ1) by
              field_simp; ring, heq]
            field_simp
          refine ⟨?_, ?_, rfl, ?_⟩
          · exact hf
          · rw [hf]; ring
          · field_simp; ring
        · push Not at hq
          obtain ⟨e1, e2, e3⟩ := U2A hP hϕ (key _ hpb0.le) (hfee _ hpb0.le) hq le_rfl
          rw [e2, e3, e1]
          refine ⟨?_, ?_, rfl, rfl⟩
          · field_simp; ring
          · field_simp; ring
      · simp only [if_neg hB]
        push Not at hB
        have hχy : μ - Λ1 < χ := by rw [hl2] at hB; linarith
        have hμϕχ : μ * ϕ ≤ c * χ := by
          have : μ - χ ≤ μ - μ * ϕ / c := by
            rw [← hl2]; convert hl2c using 1; field_simp
          have : μ * ϕ / c ≤ χ := by linarith
          rwa [div_le_iff₀ hc, mul_comm χ] at this
        have hrD : R - 2 * R * (μ - χ) / (2 * μ - χ) = μ * ϕ / χ ^ 2 := by
          rw [hpDeq]; ring
        have hχ2 : 0 < χ ^ 2 := by positivity
        have hy2 : (μ - Λ1) ^ 2 < χ ^ 2 := pow_lt_pow_left₀ hχy hy.le (by norm_num)
        have hr1 : ϕ / μ < R - 2 * R * (μ - χ) / (2 * μ - χ) := by
          rw [hrD, div_lt_div_iff₀ hμ hχ2]
          have : χ ^ 2 < μ ^ 2 := pow_lt_pow_left₀ hχμ hχ0.le (by norm_num)
          linarith [mul_lt_mul_of_pos_left this hϕ]
        have hr2 : R - 2 * R * (μ - χ) / (2 * μ - χ) < μ * ϕ / (μ - Λ1) ^ 2 := by
          rw [hrD]; exact div_lt_div_of_pos_left (by positivity) (by positivity) hy2
        have hr3 : R - 2 * R * (μ - χ) / (2 * μ - χ) ≤ c ^ 2 / (μ * ϕ) := by
          rw [hrD, div_le_div_iff₀ hχ2 (by positivity)]
          have : (μ * ϕ) * (μ * ϕ) ≤ (c * χ) * (c * χ) :=
            mul_le_mul hμϕχ hμϕχ (by positivity) (by positivity)
          linarith
        have hr4 : R - 2 * R * (μ - χ) / (2 * μ - χ) < c / (μ - Λ1) := by
          rw [hrD]
          have h1 : μ * ϕ / χ ^ 2 ≤ c / χ := by
            rw [div_le_div_iff₀ hχ2 hχ0]; linarith [mul_le_mul_of_nonneg_right hμϕχ hχ0.le]
          have h2 : c / χ < c / (μ - Λ1) := div_lt_div_of_pos_left hc hy hχy
          linarith
        obtain ⟨e1, e2, e3⟩ := U3 hP hϕ (key _ hpD0.le) (hfee _ hpD0.le) hr1 hr2 hr3 hr4
        rw [hrD] at e1 e2
        have q1 : Real.sqrt (μ * ϕ * (μ * ϕ / χ ^ 2)) = μ * ϕ / χ :=
          sqrt_of_sq (by positivity) (by field_simp)
        have q2 : Real.sqrt (μ * ϕ / (μ * ϕ / χ ^ 2)) = χ :=
          sqrt_of_sq hχ0.le (by field_simp)
        rw [q1] at e1; rw [q2] at e2
        rw [e2, e3, e1]
        have hχne : χ ≠ 0 := hχ0.ne'
        have h2χ : 2 * μ - χ ≠ 0 := by linarith
        have hf : μ * ϕ / χ ^ 2 - μ * ϕ / χ / μ = R * χ * (μ - χ) / (μ * (2 * μ - χ)) := by
          rw [show μ * ϕ / χ ^ 2 - μ * ϕ / χ / μ = ϕ * (μ - χ) / χ ^ 2 by field_simp,
            div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (μ - χ) * hcub
        refine ⟨hf, ?_, rfl, rfl⟩
        rw [hf]; field_simp
  · simp only [if_neg h1]
    have hMK : 2 * R * (μ - χ) ^ 2 / (2 * μ - χ) < (s - t) ^ 2 := by
      by_contra h; push Not at h; exact h1 (hiff.2 h)
    have hpc : R - R * t / s ≤ R - c ^ 2 / (μ * ϕ) := by
      by_contra h; push Not at h
      have := hAD2 _ hpA0 (by have : 0 < R * t / s := by positivity
                              linarith) h
      have := hD_le _ hpA0.le hpA1
      linarith
    have e : R - (R - R * t / s) = R * t / s := by ring
    have e2 : c / (R * t / s) = μ * t / s := by
      rw [div_eq_div_iff (by positivity) (by positivity), hR', hc']; field_simp
    by_cases hA : Λ1 ≤ μ - μ * t / s
    · simp only [if_pos hA]
      obtain ⟨e1, e2', e3⟩ := U1 hP hϕ (key _ hpA0.le) (hfee _ hpA0.le) (hA1 hA)
      rw [e2', e3, e1, e, e2]
      refine ⟨?_, ?_, rfl, rfl⟩
      · rw [hR', hc']; field_simp
      · rw [hR', hc']; field_simp
    · simp only [if_neg hA]
      push Not at hA
      obtain ⟨e1, e2', e3⟩ := U2B hP hϕ (key _ hpA0.le) (hfee _ hpA0.le) (hA1' hA) hpc
      rw [e2', e3, e1, e, e2]
      refine ⟨?_, ?_, rfl, rfl⟩
      · rw [hR', hc']; field_simp
      · rw [hR', hc']; field_simp

end X5FD

-- ==== module C4 ====

namespace X5FD
open FoodDeliv.Decentral Filter Topology

noncomputable def ST4 (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else if Λ1 ≤ lam2 R μ ϕ then R * Λ1 - ϕ * Λ1 / (μ - Λ1)
          else R * (2 * μ + chi R μ ϕ) * (μ - chi R μ ϕ) ^ 2 / (μ * (2 * μ - chi R μ ϕ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then
            (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else ϕ + R * μ - (c + ϕ) * Real.sqrt (R * μ / c))

theorem welfare_eq (P : Params) (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ) (p : ℝ) :
    welfare P σ fee p = (σ p (fee p)).lamD * (P.R - P.ϕ / (P.μ - ((σ p (fee p)).lamD + (σ p (fee p)).lamW)))
      + (σ p (fee p)).lamW * (P.R - P.c / (P.μ - ((σ p (fee p)).lamD + (σ p (fee p)).lamW))) := by
  simp only [welfare, restProfit, platProfit, UD, UW, Profile.total]; ring

set_option maxHeartbeats 1000000 in
theorem w_part1 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0)
    (Λ1 : ℝ) (hΛ : Λ1 ∈ Set.Ioo 0 μ) (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ)
    (hσ : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hfee : ∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) :
    welfare ⟨R, μ, c, ϕ, Λ0, Λ1⟩ σ fee (pT3 R μ c ϕ Λ1) = ST4 R μ c ϕ Λ1 := by
  obtain ⟨-, -, hD, hW⟩ := tab R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0 Λ1 hΛ σ fee hσ hfee
  rw [welfare_eq, hD, hW]
  show DT3 R μ c ϕ Λ1 * (R - ϕ / (μ - (DT3 R μ c ϕ Λ1 + WT3 R μ c ϕ Λ1))) +
      WT3 R μ c ϕ Λ1 * (R - c / (μ - (DT3 R μ c ϕ Λ1 + WT3 R μ c ϕ Λ1))) = ST4 R μ c ϕ Λ1
  have hR := R_pos hμ hc hcR
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hχ0, hχμ, hcub⟩, -, -, -, -, -, -, -, -, -⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  obtain ⟨hs2, ht2, hs0, ht0, hst, -, hsqT, hk1, -, hk3⟩ := sq_facts hμ hc hcR
  unfold DT3 WT3 ST4
  rw [hsqT, hk1, hk3]
  set s := Real.sqrt (R * μ)
  set t := Real.sqrt c
  set χ := chi R μ ϕ
  have hy : 0 < μ - Λ1 := by linarith [hΛ.2]
  have hyne : μ - Λ1 ≠ 0 := hy.ne'
  have htne : t ≠ 0 := ht0.ne'
  have hsne : s ≠ 0 := hs0.ne'
  have hχne : χ ≠ 0 := hχ0.ne'
  have h2χ : 2 * μ - χ ≠ 0 := by linarith
  have hR' : R = s ^ 2 / μ := by rw [hs2]; field_simp
  have hc' : c = t ^ 2 := ht2.symm
  have eA : ∀ x : ℝ, μ - (x + (μ - μ * t / s - x)) = μ * t / s := fun x => by ring
  have hA : Λ1 * (R - ϕ / (μ * t / s)) + (μ - μ * t / s - Λ1) * (R - c / (μ * t / s)) =
      (s - t) ^ 2 + Λ1 * (c - ϕ) * (s / (μ * t)) := by
    rw [hR', hc']; field_simp; ring
  split_ifs
  · rw [eA, hA]
  · simp only [add_zero, zero_mul]; ring
  · simp only [add_zero, zero_mul, show μ - (μ - χ) = χ by ring]
    have e : R - ϕ / χ = (R * χ - ϕ) / χ := by field_simp
    rw [e, mul_div_assoc', div_eq_div_iff hχne (by positivity)]
    linear_combination (-(μ - χ)) * hcub
  · rw [eA, hA]
  · simp only [add_zero, zero_mul, show μ - (μ - μ * t / s) = μ * t / s by ring]
    rw [hR', hc']; field_simp; ring

set_option maxHeartbeats 1000000 in
theorem w_partI (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (h1 : ϕ ≤ phi1 R μ c) :
    ∃ L : ℝ, Tendsto (ST4 R μ c ϕ) (𝓝[>] (lam1 R μ c ϕ)) (𝓝 L) ∧ L < ST4 R μ c ϕ (lam1 R μ c ϕ) := by
  have hR := R_pos hμ hc hcR
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hχ0, hχμ, hcub⟩, -, -, -, -, -, -, hlc, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  obtain ⟨hl2c, hL10, hL12, hdcL1, -⟩ := hKMc (hiff.1 h1)
  have hlamA := lam1_lt_lamA R μ c ϕ hμ hc hcR hϕ hϕc h1
  obtain ⟨hs2, ht2, hs0, ht0, hst, -, hsqT, hk1, -, -⟩ := sq_facts hμ hc hcR
  rw [hsqT] at hlamA
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set s := Real.sqrt (R * μ)
  set t := Real.sqrt c
  set χ := chi R μ ϕ
  set l1 := lam1 R μ c ϕ with hl1def
  set l2 := lam2 R μ ϕ with hl2def
  have hl1μ : l1 < μ := by rw [hl2] at hL12; linarith
  have hy : 0 < μ - l1 := by linarith
  set L := R * l1 - ϕ * l1 / (μ - l1) with hL
  refine ⟨L, ?_, ?_⟩
  · rcases hL12.lt_or_eq with h12 | h12
    · have hev : (fun Λ => R * Λ - ϕ * Λ / (μ - Λ)) =ᶠ[𝓝[>] l1] ST4 R μ c ϕ := by
        filter_upwards [Ioo_mem_nhdsGT h12] with Λ hΛ
        simp only [ST4, if_pos h1]
        rw [← hl1def, ← hl2def, if_neg (not_le.2 hΛ.1), if_pos hΛ.2.le]
      refine Tendsto.congr' hev ?_
      have hc' : ContinuousAt (fun Λ => R * Λ - ϕ * Λ / (μ - Λ)) l1 :=
        ContinuousAt.sub (by fun_prop) (ContinuousAt.div (by fun_prop) (by fun_prop) hy.ne')
      exact hc'.tendsto.mono_left nhdsWithin_le_nhds
    · have hev : (fun _ => R * (2 * μ + χ) * (μ - χ) ^ 2 / (μ * (2 * μ - χ))) =ᶠ[𝓝[>] l1]
          ST4 R μ c ϕ := by
        filter_upwards [self_mem_nhdsWithin] with Λ hΛ
        have hΛ' : l1 < Λ := hΛ
        have hΛ2 : l2 < Λ := h12 ▸ hΛ'
        simp only [ST4, if_pos h1]
        rw [← hl1def, ← hl2def, if_neg (not_le.2 hΛ'), if_neg (not_le.2 hΛ2)]
      refine Tendsto.congr' hev ?_
      have : L = R * (2 * μ + χ) * (μ - χ) ^ 2 / (μ * (2 * μ - χ)) := by
        rw [hL, h12, hl2, show μ - (μ - χ) = χ by ring]
        have h2χ : 2 * μ - χ ≠ 0 := by linarith
        have hχne : χ ≠ 0 := hχ0.ne'
        have e : R * (μ - χ) - ϕ * (μ - χ) / χ = (μ - χ) * (R * χ - ϕ) / χ := by
          field_simp
        rw [e, div_eq_div_iff hχne (by positivity)]
        linear_combination (-(μ - χ)) * hcub
      rw [this]; exact tendsto_const_nhds
  · simp only [ST4, if_pos h1]
    rw [← hl1def, if_pos le_rfl]
    rw [hk1]
    have hmem : l1 ∈ Set.Ioo 0 μ := ⟨hL10, hl1μ⟩
    have ha := (hlc l1 hmem).1 (le_trans hL12 hl2c)
    have hb : μ * ϕ / (μ - l1) ^ 2 ≤ c / (μ - l1) := by linarith
    unfold deliveryCurve at hdcL1
    rw [← hdcL1]
    have e : L = l1 * (R - μ * ϕ / (μ - l1) ^ 2) + l1 * (μ * ϕ / (μ - l1) ^ 2 - ϕ / (μ - l1)) := by
      rw [hL]; field_simp; ring
    have hyA : μ * t / s < μ - l1 := by linarith
    have h3 : (c - ϕ) / (μ - l1) < (c - ϕ) * (s / (μ * t)) := by
      rw [div_lt_iff₀ hy]
      have h4 : μ * t < (μ - l1) * s := by rwa [div_lt_iff₀ hs0] at hyA
      have h5 : 1 < s / (μ * t) * (μ - l1) := by
        rw [div_mul_eq_mul_div, one_lt_div (by positivity)]; linarith
      have : 0 < c - ϕ := by linarith
      linarith [mul_lt_mul_of_pos_left h5 this]
    have h6 : μ * ϕ / (μ - l1) ^ 2 - ϕ / (μ - l1) ≤ (c - ϕ) / (μ - l1) := by
      rw [sub_div]; linarith
    rw [e]
    have := mul_lt_mul_of_pos_left (lt_of_le_of_lt h6 h3) hL10
    have e2 : l1 * ((c - ϕ) * (s / (μ * t))) = l1 * (c - ϕ) * (s / (μ * t)) := by ring
    linarith

theorem w_partII (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕc : ϕ < c) (h1 : phi1 R μ c < ϕ) :
    MonotoneOn (ST4 R μ c ϕ) (Set.Ioo 0 μ) := by
  obtain ⟨hs2, ht2, hs0, ht0, hst, -, hsqT, hk1, -, hk3⟩ := sq_facts hμ hc hcR
  set s := Real.sqrt (R * μ)
  set t := Real.sqrt c
  have hcϕ : 0 ≤ c - ϕ := by linarith
  have hk : 0 ≤ s / (μ * t) := by positivity
  have hR : R = s ^ 2 / μ := by rw [hs2]; field_simp
  have hAk : (s - t) ^ 2 + (μ - μ * t / s) * (c - ϕ) * (s / (μ * t)) = ϕ + R * μ - (c + ϕ) * (s / t) := by
    rw [hR, ← ht2]; field_simp; ring
  intro a _ b _ hab
  simp only [ST4, if_neg (not_le.2 h1)]
  rw [hsqT, hk1, hk3]
  split_ifs with ha hb hb
  · linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hcϕ) hk]
  · rw [← hAk]
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hcϕ) hk]
  · exact absurd (le_trans hab hb) ha
  · exact le_rfl

end X5FD

-- ==== module Sol4 ====

open Filter Topology FoodDeliv.Decentral

theorem solution (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    let ϕ1 := phi1 R μ c
    let l1 := lam1 R μ c ϕ
    let l2 := lam2 R μ ϕ
    let χ := chi R μ ϕ
    -- Proposition C.4's equilibrium price `p*(Λ1)`
    let pT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then R - Real.sqrt (c / μ * R)
          else if Λ1 ≤ l2 then R - μ * ϕ / (μ - Λ1) ^ 2
          else 2 * R * (μ - χ) / (2 * μ - χ))
      else R - Real.sqrt (c / μ * R)
    -- the table: `S*(Λ1)`
    let ST : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else if Λ1 ≤ l2 then R * Λ1 - ϕ * Λ1 / (μ - Λ1)
          else R * (2 * μ + χ) * (μ - χ) ^ 2 / (μ * (2 * μ - χ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then
            (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else ϕ + R * μ - (c + ϕ) * Real.sqrt (R * μ / c))
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      welfare ⟨R, μ, c, ϕ, Λ0, Λ1⟩ σ fee (pT Λ1) = ST Λ1) ∧
    -- (i)
    (ϕ ≤ ϕ1 → ∃ L : ℝ, Tendsto ST (𝓝[>] l1) (𝓝 L) ∧ L < ST l1) ∧
    -- (ii)
    (ϕ1 < ϕ → MonotoneOn ST (Set.Ioo 0 μ)) := by
  intro _ϕ1 _l1 _l2 _χ _pT _ST
  exact ⟨fun Λ1 hΛ σ fee hσ hfee => X5FD.w_part1 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0 Λ1 hΛ σ fee hσ hfee,
    fun h => X5FD.w_partI R μ c ϕ hμ hc hcR hϕ hϕc h,
    fun h => X5FD.w_partII R μ c ϕ hμ hc hcR hϕc h⟩




