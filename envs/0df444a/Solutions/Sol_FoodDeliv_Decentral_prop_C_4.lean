-- Prove2me | solution 1 for FoodDeliv.Decentral.prop_C_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:27:06.374275+00:00
-- url     : https://prove2.me/submissions/2d7a2e65-4ab4-4d31-a44c-f7dbc3b7795f

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model
import Theorems.Thm_FoodDeliv_Decentral_cor_C_2
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_6
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_7
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_8

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


namespace X5FD
open FoodDeliv.Decentral

noncomputable def pTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then R - Real.sqrt (c / μ * R)
          else if Λ1 ≤ lam2 R μ ϕ then R - μ * ϕ / (μ - Λ1) ^ 2
          else 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ))
      else R - Real.sqrt (c / μ * R)

noncomputable def VTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
          else if Λ1 ≤ lam2 R μ ϕ then Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2)
          else 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ))
      else (Real.sqrt (R * μ) - Real.sqrt c) ^ 2

noncomputable def TTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
      if ϕ ≤ phi1 R μ c then
        (if Λ1 ≤ lam1 R μ c ϕ then μ - Real.sqrt (c * μ / R)
          else if Λ1 ≤ lam2 R μ ϕ then Λ1
          else μ - chi R μ ϕ)
      else μ - Real.sqrt (c * μ / R)

set_option maxHeartbeats 1000000 in
theorem part1 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0)
    (Λ1 : ℝ) (hΛ : Λ1 ∈ Set.Ioo 0 μ) (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ)
    (hσ : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ))
    (hfee : ∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) :
    IsOptPrice σ fee (pTf R μ c ϕ Λ1) ∧ restProfit σ fee (pTf R μ c ϕ Λ1) = VTf R μ c ϕ Λ1 ∧
      (σ (pTf R μ c ϕ Λ1) (fee (pTf R μ c ϕ Λ1))).total = TTf R μ c ϕ Λ1 := by
  unfold pTf VTf TTf
  have hR := R_pos hμ hc hcR
  obtain ⟨hA_le, ⟨hpA0, hpA1, hApA⟩, hD_le, ⟨hpD0, hpD1, hDpD⟩, hD_anti, hAD1, hAD2, hstrict,
    ⟨hχ0, hχμ, hcub⟩, hpDeq, hDpb, hdcM, hdcl2, hdcmono, hdcanti, hlc, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set K := (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 with hK
  set M := 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) with hM
  set pA := R - Real.sqrt (c / μ * R) with hpA
  set pD := 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ) with hpD
  set χ := chi R μ ϕ with hχ
  set L1 := lam1 R μ c ϕ with hL1
  set L2 := lam2 R μ ϕ with hL2
  set lc := (c - ϕ) / c * μ with hlcdef
  -- sqrt bookkeeping
  set s := Real.sqrt (R * μ) with hs
  set t := Real.sqrt c with ht
  have hs2 : s ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = c := Real.sq_sqrt hc.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hc
  have hst : t < s := Real.sqrt_lt_sqrt hc.le hcR
  have hK0 : 0 < K := by rw [hK]; exact pow_pos (by linarith) 2
  have hsqA : Real.sqrt (c / μ * R) = R * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hsqT : Real.sqrt (c * μ / R) = μ * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hTA : K / pA = μ - Real.sqrt (c * μ / R) := by
    rw [hsqT, div_eq_iff hpA0.ne', hpA, hsqA, hK]
    have e : (μ - μ * t / s) * (R - R * t / s) = μ * R * (s - t) ^ 2 / s ^ 2 := by
      field_simp
    rw [e, hs2]; field_simp
  have hμχ : μ - χ ≠ 0 := by linarith
  have h2χ : 2 * μ - χ ≠ 0 := by linarith
  have hTD : M / pD = μ - χ := by
    rw [hM, hpD]; field_simp
  have hϕμ : 0 < ϕ / μ := by positivity
  have hpAR : pA < R := by linarith
  have hpDR : pD < R := by linarith
  have hRϕμ : 0 < R - ϕ / μ := by
    rw [sub_pos, div_lt_iff₀ hμ]; linarith

  set P : Params := ⟨R, μ, c, ϕ, Λ0, Λ1⟩ with hPdef
  have hP : P.Standing := ⟨hμ, hc, hcR, hϕ.le, hϕc, hΛ0, hΛ.1, hΛ.2⟩
  obtain ⟨hcI, hcII⟩ := cor_C_2 P hP hϕ σ fee hσ hfee
  have hZ : ∀ p, R - ϕ / μ < p → restProfit σ fee p = 0 := by
    intro p hp
    have hp0 : 0 ≤ p := by linarith
    have hf := (hfee p hp0).1
    unfold restProfit
    rw [zero_region P hP p (fee p) _ (hσ p (fee p) hp0 hf) hf hp, mul_zero]
  set pa := R - c / (μ - Λ1) with hpa
  set pb := R - μ * ϕ / (μ - Λ1) ^ 2 with hpb
  set pc := R - c ^ 2 / (μ * ϕ) with hpc
  have hμΛ : 0 < μ - Λ1 := by linarith [hΛ.2]
  have hDpbE : Dcurve R μ ϕ pb = Λ1 * pb := hDpb Λ1 hΛ
  have hEM : Λ1 * pb ≤ M := hdcM Λ1 hΛ
  have hpa1 : pa ≤ R - ϕ / μ := by
    have : ϕ / μ ≤ c / (μ - Λ1) := by
      calc ϕ / μ ≤ c / μ := div_le_div_of_nonneg_right hϕc.le hμ.le
        _ ≤ c / (μ - Λ1) := div_le_div_of_nonneg_left hc.le hμΛ (by linarith [hΛ.1])
    linarith
  have hpb1 : pb ≤ R - ϕ / μ := by
    have : ϕ / μ ≤ μ * ϕ / (μ - Λ1) ^ 2 := by
      have h1 : (μ - Λ1) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hμΛ.le (by linarith [hΛ.1]) 2
      rw [show ϕ / μ = μ * ϕ / μ ^ 2 by field_simp]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
    linarith
  have hpc1 : pc ≤ R - ϕ / μ := by
    have : ϕ / μ ≤ c ^ 2 / (μ * ϕ) := by
      rw [show ϕ / μ = ϕ ^ 2 / (μ * ϕ) by field_simp]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hϕ.le hϕc.le 2) (by positivity)
    linarith
  have F2 : Λ1 ≤ lc → pc ≤ pa := by
    intro h
    have h' : Λ1 * c ≤ (c - ϕ) * μ := by
      have := mul_le_mul_of_nonneg_right h hc.le
      rwa [show (c - ϕ) / c * μ * c = (c - ϕ) * μ by field_simp] at this
    have h3 : μ * ϕ ≤ c * (μ - Λ1) := by
      have e : c * (μ - Λ1) - μ * ϕ = (c - ϕ) * μ - Λ1 * c := by ring
      linarith [e]
    have : c / (μ - Λ1) ≤ c ^ 2 / (μ * ϕ) := by
      rw [show c / (μ - Λ1) = c ^ 2 / (c * (μ - Λ1)) by
        rw [pow_two, mul_div_mul_left c (μ - Λ1) hc.ne']]
      exact div_le_div_of_nonneg_left (sq_nonneg c) (by positivity) h3
    linarith
  have hpbD1 : Λ1 ≤ L2 → pD ≤ pb := by
    intro h
    have h1 : χ ≤ μ - Λ1 := by rw [hl2] at h; linarith
    have : μ * ϕ / (μ - Λ1) ^ 2 ≤ μ * ϕ / χ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hχ0.le h1 2)
    rw [hpDeq]; linarith
  have hpbD2 : L2 < Λ1 → pb < pD := by
    intro h
    have h1 : μ - Λ1 < χ := by rw [hl2] at h; linarith
    have : μ * ϕ / χ ^ 2 < μ * ϕ / (μ - Λ1) ^ 2 :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (pow_lt_pow_left₀ h1 hμΛ.le (by norm_num))
    rw [hpDeq]; linarith
  have A_lt_L : ∀ p, 0 < p → pa < p → p < R → Acurve R μ c p < p * Λ1 := by
    intro p hp h1 h2
    have hRp : 0 < R - p := by linarith
    have h3 : R - p < c / (μ - Λ1) := by linarith
    rw [lt_div_iff₀ hμΛ] at h3
    have : μ - Λ1 < c / (R - p) := by rw [lt_div_iff₀ hRp]; linarith
    unfold Acurve; apply mul_lt_mul_of_pos_left _ hp; linarith
  have A_pa : Acurve R μ c pa = pa * Λ1 := by
    have : c / (R - pa) = μ - Λ1 := by
      rw [hpa, show R - (R - c / (μ - Λ1)) = c / (μ - Λ1) by ring]; field_simp
    unfold Acurve; rw [this]; ring
  -- regions
  have rIA : Λ1 ≤ lc → ∀ p, 0 ≤ p → p ≤ pa → restProfit σ fee p = Acurve R μ c p :=
    fun h p hp h1 => (hcI h p hp).1 h1
  have rIL : Λ1 ≤ lc → ∀ p, 0 ≤ p → pa < p → p ≤ pb → restProfit σ fee p = p * Λ1 :=
    fun h p hp h1 h2 => (hcI h p hp).2.1 ⟨h1, h2⟩
  have rID : Λ1 ≤ lc → ∀ p, 0 ≤ p → pb < p → p ≤ R - ϕ / μ →
      restProfit σ fee p = Dcurve R μ ϕ p :=
    fun h p hp h1 h2 => (hcI h p hp).2.2 ⟨h1, h2⟩
  have rIIA : lc < Λ1 → ∀ p, 0 ≤ p → p ≤ pc → restProfit σ fee p = Acurve R μ c p :=
    fun h p hp h1 => (hcII h p hp).1 h1
  have rIID : lc < Λ1 → ∀ p, 0 ≤ p → pc < p → p ≤ R - ϕ / μ →
      restProfit σ fee p = Dcurve R μ ϕ p :=
    fun h p hp h1 h2 => (hcII h p hp).2 ⟨h1, h2⟩
  have boundI : Λ1 ≤ lc → ∀ V, K ≤ V → Λ1 * pb ≤ V →
      (∀ p, 0 ≤ p → pb < p → p ≤ R - ϕ / μ → Dcurve R μ ϕ p ≤ V) →
      ∀ p, 0 ≤ p → restProfit σ fee p ≤ V := by
    intro h V hKV hEV hDV p hp
    by_cases h1 : p ≤ pa
    · rw [rIA h p hp h1]; exact (hA_le p hp (h1.trans hpa1)).trans hKV
    by_cases h2 : p ≤ pb
    · rw [rIL h p hp (not_le.mp h1) h2]
      have := mul_le_mul_of_nonneg_right h2 hΛ.1.le
      linarith
    by_cases h3 : p ≤ R - ϕ / μ
    · rw [rID h p hp (not_le.mp h2) h3]; exact hDV p hp (not_le.mp h2) h3
    · rw [hZ p (not_le.mp h3)]; linarith
  have boundII : lc < Λ1 → ∀ V, K ≤ V → M ≤ V → ∀ p, 0 ≤ p → restProfit σ fee p ≤ V := by
    intro h V hKV hMV p hp
    by_cases h1 : p ≤ pc
    · rw [rIIA h p hp h1]; exact (hA_le p hp (h1.trans hpc1)).trans hKV
    by_cases h3 : p ≤ R - ϕ / μ
    · rw [rIID h p hp (not_le.mp h1) h3]; exact (hD_le p hp h3).trans hMV
    · rw [hZ p (not_le.mp h3)]; linarith
  by_cases hϕ1 : ϕ ≤ phi1 R μ c
  · have hKM := hiff.mp hϕ1
    obtain ⟨hl2c, hl10, hl12, hdcl1, hpApD⟩ := hKMc hKM
    simp only [if_pos hϕ1]
    by_cases ha : Λ1 ≤ L1
    · simp only [if_pos ha]
      have hI : Λ1 ≤ lc := by linarith
      have hEK : Λ1 * pb ≤ K := by
        rw [← hdcl1]; exact hdcmono.monotoneOn ⟨hΛ.1, by linarith⟩ ⟨hl10, hl12⟩ ha
      have hpDpb := hpbD1 (by linarith)
      have hDb : ∀ p, 0 ≤ p → pb < p → p ≤ R - ϕ / μ → Dcurve R μ ϕ p ≤ K := by
        intro p _ h1 h2; have := hD_anti pb p hpDpb h1 h2; linarith
      have hval : restProfit σ fee pA = K := by
        have : pA ≤ pa := by
          by_contra h; push Not at h
          by_cases h' : pA ≤ pb
          · have hL := mul_le_mul_of_nonneg_right h' hΛ.1.le
            have := A_lt_L pA hpA0 h (by linarith)
            linarith
          · push Not at h'
            have h1 := hD_anti pb pA hpDpb h' hpA1
            have h2 := hAD2 pA hpA0 (by linarith) (by linarith [F2 hI])
            linarith
        rw [rIA hI pA hpA0.le this, hApA]
      obtain ⟨h1, h2, h3⟩ := fin_step σ fee K pA hpA0 (boundI hI K le_rfl hEK hDb) hval
      exact ⟨h1, h2, by rw [h3, hTA]⟩
    · simp only [if_neg ha]
      push Not at ha
      by_cases hb : Λ1 ≤ L2
      · simp only [if_pos hb]
        have hI : Λ1 ≤ lc := le_trans hb hl2c
        have hKE : K ≤ Λ1 * pb := by
          rw [← hdcl1]; exact (hdcmono ⟨hl10, hl12⟩ ⟨hΛ.1, hb⟩ ha).le
        have hpDpb := hpbD1 hb
        have hpb0 : 0 < pb := by
          by_contra h; push Not at h
          have : Λ1 * pb ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hΛ.1.le h
          linarith
        have hval : restProfit σ fee pb = Λ1 * pb := by
          by_cases h : pb ≤ pa
          · have heq : pa = pb := le_antisymm ((hlc Λ1 hΛ).mp hI) h
            rw [rIA hI pb hpb0.le h, ← heq, A_pa]; ring
          · push Not at h; rw [rIL hI pb hpb0.le h le_rfl]; ring
        have hDb : ∀ p, 0 ≤ p → pb < p → p ≤ R - ϕ / μ → Dcurve R μ ϕ p ≤ Λ1 * pb := by
          intro p _ h1 h2; have := hD_anti pb p hpDpb h1 h2; linarith
        obtain ⟨h1, h2, h3⟩ := fin_step σ fee (Λ1 * pb) pb hpb0
          (boundI hI _ hKE le_rfl hDb) hval
        refine ⟨h1, h2, ?_⟩; rw [h3]; field_simp
      · simp only [if_neg hb]
        push Not at hb
        have hval : restProfit σ fee pD = M := by
          by_cases hI : Λ1 ≤ lc
          · rw [rID hI pD hpD0.le (hpbD2 hb) hpD1, hDpD]
          · push Not at hI
            by_cases h : pD ≤ pc
            · rw [rIIA hI pD hpD0.le h]
              have := hAD1 pD hpD0 (by linarith) h
              have := hA_le pD hpD0.le hpD1
              linarith
            · rw [rIID hI pD hpD0.le (not_le.mp h) hpD1, hDpD]
        have hbd : ∀ p, 0 ≤ p → restProfit σ fee p ≤ M := by
          by_cases hI : Λ1 ≤ lc
          · exact boundI hI M hKM hEM (fun p hp _ h2 => hD_le p hp h2)
          · exact boundII (not_le.mp hI) M hKM le_rfl
        obtain ⟨h1, h2, h3⟩ := fin_step σ fee M pD hpD0 hbd hval
        exact ⟨h1, h2, by rw [h3, hTD]⟩
  · simp only [if_neg hϕ1]
    have hMK : M < K := not_le.mp (fun h => hϕ1 (hiff.mpr h))
    have hval : restProfit σ fee pA = K := by
      by_cases hI : Λ1 ≤ lc
      · have : pA ≤ pa := by
          by_contra h; push Not at h
          have h2 := hAD2 pA hpA0 (by linarith) (by linarith [F2 hI])
          have := hD_le pA hpA0.le hpA1
          linarith
        rw [rIA hI pA hpA0.le this, hApA]
      · push Not at hI
        have : pA ≤ pc := by
          by_contra h; push Not at h
          have h2 := hAD2 pA hpA0 (by linarith) h
          have := hD_le pA hpA0.le hpA1
          linarith
        rw [rIIA hI pA hpA0.le this, hApA]
    have hbd : ∀ p, 0 ≤ p → restProfit σ fee p ≤ K := by
      by_cases hI : Λ1 ≤ lc
      · exact boundI hI K le_rfl (by linarith) (fun p hp _ h2 => (hD_le p hp h2).trans hMK.le)
      · exact boundII (not_le.mp hI) K le_rfl hMK.le
    obtain ⟨h1, h2, h3⟩ := fin_step σ fee K pA hpA0 hbd hval
    exact ⟨h1, h2, by rw [h3, hTA]⟩

set_option maxHeartbeats 1000000 in
theorem part2 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    ϕ ≤ phi1 R μ c → ∀ a ∈ Set.Ioc 0 (lam1 R μ c ϕ), ∀ b ∈ Set.Ioo (lam1 R μ c ϕ) μ,
      pTf R μ c ϕ a < pTf R μ c ϕ b := by
  unfold pTf
  have hR := R_pos hμ hc hcR
  obtain ⟨hA_le, ⟨hpA0, hpA1, hApA⟩, hD_le, ⟨hpD0, hpD1, hDpD⟩, hD_anti, hAD1, hAD2, hstrict,
    ⟨hχ0, hχμ, hcub⟩, hpDeq, hDpb, hdcM, hdcl2, hdcmono, hdcanti, hlc, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set K := (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 with hK
  set M := 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) with hM
  set pA := R - Real.sqrt (c / μ * R) with hpA
  set pD := 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ) with hpD
  set χ := chi R μ ϕ with hχ
  set L1 := lam1 R μ c ϕ with hL1
  set L2 := lam2 R μ ϕ with hL2
  set lc := (c - ϕ) / c * μ with hlcdef
  -- sqrt bookkeeping
  set s := Real.sqrt (R * μ) with hs
  set t := Real.sqrt c with ht
  have hs2 : s ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = c := Real.sq_sqrt hc.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hc
  have hst : t < s := Real.sqrt_lt_sqrt hc.le hcR
  have hK0 : 0 < K := by rw [hK]; exact pow_pos (by linarith) 2
  have hsqA : Real.sqrt (c / μ * R) = R * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hsqT : Real.sqrt (c * μ / R) = μ * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hTA : K / pA = μ - Real.sqrt (c * μ / R) := by
    rw [hsqT, div_eq_iff hpA0.ne', hpA, hsqA, hK]
    have e : (μ - μ * t / s) * (R - R * t / s) = μ * R * (s - t) ^ 2 / s ^ 2 := by
      field_simp
    rw [e, hs2]; field_simp
  have hμχ : μ - χ ≠ 0 := by linarith
  have h2χ : 2 * μ - χ ≠ 0 := by linarith
  have hTD : M / pD = μ - χ := by
    rw [hM, hpD]; field_simp
  have hϕμ : 0 < ϕ / μ := by positivity
  have hpAR : pA < R := by linarith
  have hpDR : pD < R := by linarith
  have hRϕμ : 0 < R - ϕ / μ := by
    rw [sub_pos, div_lt_iff₀ hμ]; linarith

  intro hϕ1 a ha b hb
  simp only [if_pos hϕ1, if_pos ha.2, if_neg (not_le.mpr hb.1)]
  obtain ⟨hl2c, hl10, hl12, hdcl1, hpApD⟩ := hKMc (hiff.mp hϕ1)
  split_ifs with h
  · have h1 : χ ≤ μ - b := by rw [hl2] at h; linarith
    have hμb : 0 < μ - b := by linarith [hb.2]
    have : μ * ϕ / (μ - b) ^ 2 ≤ μ * ϕ / χ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hχ0.le h1 2)
    rw [hpDeq] at hpApD; linarith
  · exact hpApD

set_option maxHeartbeats 1000000 in
theorem part3 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    MonotoneOn (VTf R μ c ϕ) (Set.Ioo 0 μ) := by
  unfold VTf
  have hR := R_pos hμ hc hcR
  obtain ⟨hA_le, ⟨hpA0, hpA1, hApA⟩, hD_le, ⟨hpD0, hpD1, hDpD⟩, hD_anti, hAD1, hAD2, hstrict,
    ⟨hχ0, hχμ, hcub⟩, hpDeq, hDpb, hdcM, hdcl2, hdcmono, hdcanti, hlc, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set K := (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 with hK
  set M := 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) with hM
  set pA := R - Real.sqrt (c / μ * R) with hpA
  set pD := 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ) with hpD
  set χ := chi R μ ϕ with hχ
  set L1 := lam1 R μ c ϕ with hL1
  set L2 := lam2 R μ ϕ with hL2
  set lc := (c - ϕ) / c * μ with hlcdef
  -- sqrt bookkeeping
  set s := Real.sqrt (R * μ) with hs
  set t := Real.sqrt c with ht
  have hs2 : s ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = c := Real.sq_sqrt hc.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hc
  have hst : t < s := Real.sqrt_lt_sqrt hc.le hcR
  have hK0 : 0 < K := by rw [hK]; exact pow_pos (by linarith) 2
  have hsqA : Real.sqrt (c / μ * R) = R * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hsqT : Real.sqrt (c * μ / R) = μ * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hTA : K / pA = μ - Real.sqrt (c * μ / R) := by
    rw [hsqT, div_eq_iff hpA0.ne', hpA, hsqA, hK]
    have e : (μ - μ * t / s) * (R - R * t / s) = μ * R * (s - t) ^ 2 / s ^ 2 := by
      field_simp
    rw [e, hs2]; field_simp
  have hμχ : μ - χ ≠ 0 := by linarith
  have h2χ : 2 * μ - χ ≠ 0 := by linarith
  have hTD : M / pD = μ - χ := by
    rw [hM, hpD]; field_simp
  have hϕμ : 0 < ϕ / μ := by positivity
  have hpAR : pA < R := by linarith
  have hpDR : pD < R := by linarith
  have hRϕμ : 0 < R - ϕ / μ := by
    rw [sub_pos, div_lt_iff₀ hμ]; linarith

  by_cases hϕ1 : ϕ ≤ phi1 R μ c
  · have hKM := hiff.mp hϕ1
    obtain ⟨hl2c, hl10, hl12, hdcl1, hpApD⟩ := hKMc hKM
    have hdc_ge : ∀ x ∈ Set.Ioo 0 μ, L1 < x → x ≤ L2 →
        K ≤ x * (R - μ * ϕ / (μ - x) ^ 2) := by
      intro x hx h1 h2; rw [← hdcl1]; exact (hdcmono ⟨hl10, hl12⟩ ⟨hx.1, h2⟩ h1).le
    have hdc_le : ∀ x ∈ Set.Ioo 0 μ, x * (R - μ * ϕ / (μ - x) ^ 2) ≤ M := hdcM
    intro a ha b hb hab
    simp only [if_pos hϕ1]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
    all_goals first
      | exact le_rfl
      | exact hKM
      | (exfalso; linarith)
      | exact hdc_ge b hb (by linarith) (by linarith)
      | exact hdc_le a ha
      | exact hdcmono.monotoneOn ⟨ha.1, by assumption⟩ ⟨hb.1, by assumption⟩ hab
  · simp only [if_neg hϕ1]
    exact monotoneOn_const

set_option maxHeartbeats 1000000 in
theorem part4 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
      c / (2 * Real.sqrt (R * μ / c) - 1) ≤ phi1 R μ c ∧ μ - Real.sqrt (c * μ / R) < lam2 R μ ϕ := by
  have hR := R_pos hμ hc hcR
  obtain ⟨hA_le, ⟨hpA0, hpA1, hApA⟩, hD_le, ⟨hpD0, hpD1, hDpD⟩, hD_anti, hAD1, hAD2, hstrict,
    ⟨hχ0, hχμ, hcub⟩, hpDeq, hDpb, hdcM, hdcl2, hdcmono, hdcanti, hlc, hKMc, hiff⟩ :=
    facts R μ c ϕ hμ hc hcR hϕ hϕc
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set K := (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 with hK
  set M := 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) with hM
  set pA := R - Real.sqrt (c / μ * R) with hpA
  set pD := 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ) with hpD
  set χ := chi R μ ϕ with hχ
  set L1 := lam1 R μ c ϕ with hL1
  set L2 := lam2 R μ ϕ with hL2
  set lc := (c - ϕ) / c * μ with hlcdef
  -- sqrt bookkeeping
  set s := Real.sqrt (R * μ) with hs
  set t := Real.sqrt c with ht
  have hs2 : s ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = c := Real.sq_sqrt hc.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hc
  have hst : t < s := Real.sqrt_lt_sqrt hc.le hcR
  have hK0 : 0 < K := by rw [hK]; exact pow_pos (by linarith) 2
  have hsqA : Real.sqrt (c / μ * R) = R * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hsqT : Real.sqrt (c * μ / R) = μ * t / s := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, mul_pow, ht2, hs2]; field_simp
  have hTA : K / pA = μ - Real.sqrt (c * μ / R) := by
    rw [hsqT, div_eq_iff hpA0.ne', hpA, hsqA, hK]
    have e : (μ - μ * t / s) * (R - R * t / s) = μ * R * (s - t) ^ 2 / s ^ 2 := by
      field_simp
    rw [e, hs2]; field_simp
  have hμχ : μ - χ ≠ 0 := by linarith
  have h2χ : 2 * μ - χ ≠ 0 := by linarith
  have hTD : M / pD = μ - χ := by
    rw [hM, hpD]; field_simp
  have hϕμ : 0 < ϕ / μ := by positivity
  have hpAR : pA < R := by linarith
  have hpDR : pD < R := by linarith
  have hRϕμ : 0 < R - ϕ / μ := by
    rw [sub_pos, div_lt_iff₀ hμ]; linarith

  intro hϕs
  have hu : Real.sqrt (R * μ / c) = s / t := by
    apply sqrt_of_sq (by positivity)
    rw [div_pow, hs2, ht2]
  rw [hu] at hϕs ⊢
  set x := μ * t / s with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < μ := by
    rw [hx, div_lt_iff₀ hs0]; exact mul_lt_mul_of_pos_left hst hμ
  have hR' : R = s ^ 2 / μ := by rw [eq_div_iff hμ.ne']; linarith
  have h2s : 0 < 2 * s - t := by linarith
  have hg : c / (2 * (s / t) - 1) = R * x ^ 3 / (μ * (2 * μ - x)) := by
    rw [hx, ← ht2, hR']
    have : 2 * (s / t) - 1 = (2 * s - t) / t := by field_simp
    rw [this]
    have : 2 * μ - μ * t / s = μ * (2 * s - t) / s := by field_simp
    rw [this]
    field_simp
  have hϕeq : ϕ = R * χ ^ 3 / (μ * (2 * μ - χ)) := by
    rw [eq_div_iff (by positivity)]; exact hcub
  constructor
  · obtain ⟨h10, h1μ, hf1⟩ := chi1_spec hμ hc hcR
    rw [hg, show phi1 R μ c = R * chi1 R μ c ^ 3 / (μ * (2 * μ - chi1 R μ c)) from rfl,
      g_le_iff hR hμ hx0.le hx1.le h10.le h1μ.le,
      ← f_le_iff hR hμ hx0.le hx1.le h10.le h1μ.le, hf1]
    have h2x : 0 < 2 * μ - x := by linarith
    rw [le_div_iff₀ h2x, hx, ← hs, ← ht]
    have e1 : μ - μ * t / s = μ * (s - t) / s := by field_simp
    have e2 : 2 * μ - μ * t / s = μ * (2 * s - t) / s := by field_simp
    rw [e1, e2, hR']
    have e : 2 * (s ^ 2 / μ) * (μ * (s - t) / s) ^ 2 = (s - t) ^ 2 * (μ * (2 * s) / s) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ hs0.le
    exact mul_le_mul_of_nonneg_left (by linarith) hμ.le
  · have : χ < x := by
      by_contra h; push Not at h
      have := (g_le_iff hR hμ hx0.le hx1.le hχ0.le hχμ.le).mpr h
      rw [← hg, ← hϕeq] at this; linarith
    rw [hsqT]; show μ - x < μ - χ; linarith


end X5FD

open FoodDeliv.Decentral X5FD

theorem solution (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    let ϕ1 := phi1 R μ c
    let l1 := lam1 R μ c ϕ
    let l2 := lam2 R μ ϕ
    let χ := chi R μ ϕ
    -- the table: `p*(Λ1)`, `Π*(Λ1)` and `λ*_D + λ*_W`
    let pT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then R - Real.sqrt (c / μ * R)
          else if Λ1 ≤ l2 then R - μ * ϕ / (μ - Λ1) ^ 2
          else 2 * R * (μ - χ) / (2 * μ - χ))
      else R - Real.sqrt (c / μ * R)
    let VT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
          else if Λ1 ≤ l2 then Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2)
          else 2 * R * (μ - χ) ^ 2 / (2 * μ - χ))
      else (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
    let TT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then μ - Real.sqrt (c * μ / R)
          else if Λ1 ≤ l2 then Λ1
          else μ - χ)
      else μ - Real.sqrt (c * μ / R)
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      IsOptPrice σ fee (pT Λ1) ∧ restProfit σ fee (pT Λ1) = VT Λ1 ∧
        (σ (pT Λ1) (fee (pT Λ1))).total = TT Λ1) ∧
    -- (i)
    (ϕ ≤ ϕ1 → ∀ a ∈ Set.Ioc 0 l1, ∀ b ∈ Set.Ioo l1 μ, pT a < pT b) ∧
    -- (ii)
    MonotoneOn VT (Set.Ioo 0 μ) ∧
    -- (iii)
    (ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
      c / (2 * Real.sqrt (R * μ / c) - 1) ≤ ϕ1 ∧ μ - Real.sqrt (c * μ / R) < l2) := by
  intro _ϕ1 _l1 _l2 _χ _pT _VT _TT
  exact ⟨fun Λ1 hΛ σ fee hσ hfee => part1 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0 Λ1 hΛ σ fee hσ hfee,
    part2 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0, part3 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0, part4 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0⟩
