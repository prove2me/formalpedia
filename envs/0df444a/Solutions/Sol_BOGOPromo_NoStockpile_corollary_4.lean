-- Prove2me | solution 1 for BOGOPromo.NoStockpile.corollary_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:29:04.865998+00:00
-- url     : https://prove2.me/submissions/f294d454-f731-4f5b-adc0-11016eb6e7db

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model
import Theorems.Thm_BOGOPromo_NoStockpile_proposition_2a
import Theorems.Thm_BOGOPromo_NoStockpile_proposition_4a
import Theorems.Thm_BOGOPromo_NoStockpile_np_equilibrium
import Theorems.Thm_BOGOPromo_NoStockpile_cBar_le_cTilde

namespace BOGOPromo.NoStockpile.Cor4Aux

open BOGOPromo.NoStockpile

/-- In the region `0 ≤ c < c̄(θ)`: `c (1 + 2θ) < θ (4θ − 1)` and `θ > 1/2`. -/
lemma region (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc : c < cBar θ) :
    c * (1 + 2 * θ) < θ * (4 * θ - 1) ∧ 1 / 2 < θ := by
  unfold cBar at hc
  have hs : 0 < 1 + 2 * θ := by linarith
  have hq0 : 0 ≤ θ / (1 + θ) := by positivity
  have hq1 : θ / (1 + θ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hsq : θ / (1 + θ) ≤ Real.sqrt (θ / (1 + θ)) := by
    rw [Real.le_sqrt hq0 hq0]; nlinarith
  have hsq0 : 0 ≤ Real.sqrt (θ / (1 + θ)) := Real.sqrt_nonneg _
  have h1 : c < θ * (4 * θ - 1) / (1 + 2 * θ) := by nlinarith
  refine ⟨by rwa [lt_div_iff₀ hs] at h1, ?_⟩
  by_contra hθ
  push Not at hθ
  have h2 : c < θ * (4 * θ - 1) / (1 + 2 * θ) - 2 * (1 - θ) * (θ / (1 + θ)) := by nlinarith
  have h3 : θ * (4 * θ - 1) / (1 + 2 * θ) - 2 * (1 - θ) * (θ / (1 + θ)) =
      θ * (8 * θ ^ 2 + θ - 3) / ((1 + 2 * θ) * (1 + θ)) := by
    field_simp; ring
  rw [h3] at h2
  have h4 : θ * (8 * θ ^ 2 + θ - 3) / ((1 + 2 * θ) * (1 + θ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith
    · positivity
  linarith

lemma idRb (θ c : ℝ) (hθ0 : 0 < θ) :
    (θ * (8 - 7 * θ + 8 * θ ^ 2) + (1 + 2 * θ) * (c ^ 2 * (1 + 2 * θ) - 6 * c * θ)) /
        (16 * θ * (1 + 2 * θ)) =
      ((3 * θ - c - 2 * c * θ) ^ 2 + 8 * θ * (1 - θ) ^ 2) / (16 * θ * (1 + 2 * θ)) := by
  congr 1; ring

lemma idRd (θ c : ℝ) (hθ0 : 0 < θ) :
    (θ * (4 + θ + 13 * θ ^ 2) +
          (1 + 2 * θ) * (1 + θ) * (c ^ 2 * (1 + 2 * θ) - 6 * c * θ)) /
        (16 * θ * (1 + 2 * θ) * (1 + θ)) =
      ((1 + θ) * (3 * θ - c - 2 * c * θ) ^ 2 + 4 * θ * (1 - θ) ^ 2) /
        (16 * θ * (1 + 2 * θ) * (1 + θ)) := by
  congr 1; ring

lemma idM (θ c : ℝ) (hθ0 : 0 < θ) :
    (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) =
      2 * (3 * θ - c - 2 * c * θ) ^ 2 / (16 * θ * (1 + 2 * θ)) := by
  have : 0 < 1 + 2 * θ := by linarith
  field_simp; ring

set_option maxHeartbeats 1000000 in
/-- Pointwise comparisons (parts 2–4 of Corollary 4 at a fixed `θ`). -/
lemma pointwise (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c)
    (hreg : c * (1 + 2 * θ) < θ * (4 * θ - 1)) :
    let M := (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ))
    let Rb := (θ * (8 - 7 * θ + 8 * θ ^ 2) + (1 + 2 * θ) * (c ^ 2 * (1 + 2 * θ) - 6 * c * θ)) /
        (16 * θ * (1 + 2 * θ))
    let Rd := (θ * (4 + θ + 13 * θ ^ 2) +
          (1 + 2 * θ) * (1 + θ) * (c ^ 2 * (1 + 2 * θ) - 6 * c * θ)) /
        (16 * θ * (1 + 2 * θ) * (1 + θ))
    let pg := (c * (1 + 2 * θ) + θ * (5 + 4 * θ)) / (4 * (1 + 2 * θ))
    let pd := (c + θ * (7 + 3 * c) + θ ^ 2 * (11 + 2 * c)) / (4 * (1 + 2 * θ) * (1 + θ))
    (1 - c) ^ 2 / 8 < Rb ∧ (1 - c) ^ 2 / 4 + (1 - c) ^ 2 / 8 < M + Rb ∧
    (θ < 1 → Rd < Rb ∧ M + Rd < M + Rb) ∧ (θ = 1 → Rb = Rd) ∧
    (θ < 1 → Rd / (M + Rd) < Rb / (M + Rb) ∧
      (1 - c) ^ 2 / 8 / ((1 - c) ^ 2 / 4 + (1 - c) ^ 2 / 8) < Rb / (M + Rb)) ∧
    (θ < 1 → pg < pd) ∧
    pd - pg = θ * (1 - θ) / (2 * (1 + θ)) ∧
    Rb - Rd = (1 - θ) ^ 2 / (4 * (1 + θ)) ∧
    Rb / (M + Rb) = ((3 * θ - c - 2 * c * θ) ^ 2 + 8 * θ * (1 - θ) ^ 2) /
      (3 * (3 * θ - c - 2 * c * θ) ^ 2 + 8 * θ * (1 - θ) ^ 2) := by
  intro M Rb Rd pg pd
  have hs : 0 < 1 + 2 * θ := by linarith
  have h1θ : 0 < 1 + θ := by linarith
  have hc1 : c < 1 := by nlinarith
  set u := (3 * θ - c - 2 * c * θ) ^ 2 with hu
  have hx : 0 < 3 * θ - c - 2 * c * θ := by nlinarith
  have hu0 : 0 < u := by positivity
  have hK : 0 ≤ θ * (1 - θ) ^ 2 := by positivity
  have hD : 0 < 16 * θ * (1 + 2 * θ) := by positivity
  have hD' : 0 < 16 * θ * (1 + 2 * θ) * (1 + θ) := by positivity
  have eRb : Rb = (u + 8 * θ * (1 - θ) ^ 2) / (16 * θ * (1 + 2 * θ)) := idRb θ c hθ0
  have eRd : Rd = ((1 + θ) * u + 4 * θ * (1 - θ) ^ 2) / (16 * θ * (1 + 2 * θ) * (1 + θ)) :=
    idRd θ c hθ0
  have eM : M = 2 * u / (16 * θ * (1 + 2 * θ)) := idM θ c hθ0
  have hM0 : 0 < M := by rw [eM]; positivity
  have hRb0 : 0 < Rb := by rw [eRb]; positivity
  have hRd0 : 0 < Rd := by rw [eRd]; positivity
  have gap : Rb - Rd = (1 - θ) ^ 2 / (4 * (1 + θ)) := by
    rw [eRb, eRd]; field_simp; ring
  have pgap : pd - pg = θ * (1 - θ) / (2 * (1 + θ)) := by
    simp only [pd, pg]; field_simp; ring
  have share : Rb / (M + Rb) = (u + 8 * θ * (1 - θ) ^ 2) / (3 * u + 8 * θ * (1 - θ) ^ 2) := by
    rw [eRb, eM]; field_simp; ring
  -- `Rb - (1-c)^2/8` and `M + Rb - 3(1-c)^2/8`
  have hRbN : Rb - (1 - c) ^ 2 / 8 =
      ((1 + 2 * θ) * (c - θ) ^ 2 + 6 * θ * (1 - θ) ^ 2) / (16 * θ * (1 + 2 * θ)) := by
    rw [eRb, hu]; field_simp; ring
  have hSN : M + Rb - ((1 - c) ^ 2 / 4 + (1 - c) ^ 2 / 8) =
      (3 * (1 + 2 * θ) * (c - θ) ^ 2 + 2 * θ * (1 - θ) ^ 2) / (16 * θ * (1 + 2 * θ)) := by
    rw [eRb, eM, hu]; field_simp; ring
  have hpos : 0 < (c - θ) ^ 2 ∨ 0 < (1 - θ) ^ 2 := by
    rcases lt_or_eq_of_le hθ1 with h | h
    · right; have : 0 < 1 - θ := by linarith
      positivity
    · left; have : c - θ ≠ 0 := by rw [h]; linarith
      positivity
  have hθK : 0 < θ * (1 - θ) ^ 2 ∨ θ = 1 := by
    rcases lt_or_eq_of_le hθ1 with h | h
    · left; have : 0 < 1 - θ := by linarith
      positivity
    · right; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, pgap, gap, share⟩
  · have : 0 < Rb - (1 - c) ^ 2 / 8 := by
      rw [hRbN]; apply div_pos _ hD
      rcases hpos with h | h <;> nlinarith
    linarith
  · have : 0 < M + Rb - ((1 - c) ^ 2 / 4 + (1 - c) ^ 2 / 8) := by
      rw [hSN]; apply div_pos _ hD
      rcases hpos with h | h <;> nlinarith
    linarith
  · intro h
    have : 0 < (1 - θ) ^ 2 / (4 * (1 + θ)) := by
      have : 0 < 1 - θ := by linarith
      positivity
    constructor <;> linarith
  · intro h
    have : (1 - θ) ^ 2 / (4 * (1 + θ)) = 0 := by rw [h]; ring
    linarith
  · intro h
    have h1 : 0 < 1 - θ := by linarith
    have hg : 0 < (1 - θ) ^ 2 / (4 * (1 + θ)) := by positivity
    constructor
    · rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      have hlt : Rd < Rb := by linarith
      have := mul_lt_mul_of_pos_left hlt hM0
      linear_combination this
    · have e : (1 - c) ^ 2 / 8 / ((1 - c) ^ 2 / 4 + (1 - c) ^ 2 / 8) = 1 / 3 := by
        have h1c : 1 - c ≠ 0 := by linarith
        have : (1 - c) ^ 2 ≠ 0 := pow_ne_zero 2 h1c
        field_simp; ring
      rw [e, share, div_lt_div_iff₀ (by norm_num) (by positivity)]
      have : 0 < θ * (1 - θ) ^ 2 := by positivity
      nlinarith
  · intro h
    have h1 : 0 < 1 - θ := by linarith
    have : 0 < θ * (1 - θ) / (2 * (1 + θ)) := by positivity
    linarith

lemma mono_gap (θ₁ θ₂ : ℝ) (h1 : 1 / 2 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ ≤ 1) :
    θ₂ * (1 - θ₂) / (2 * (1 + θ₂)) < θ₁ * (1 - θ₁) / (2 * (1 + θ₁)) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have : 0 < (θ₂ - θ₁) * (θ₁ * θ₂ + θ₁ + θ₂ - 1) := by
    apply mul_pos <;> nlinarith
  nlinarith

lemma mono_adv (θ₁ θ₂ : ℝ) (h1 : 0 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ ≤ 1) :
    (1 - θ₂) ^ 2 / (4 * (1 + θ₂)) < (1 - θ₁) ^ 2 / (4 * (1 + θ₁)) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have ha : (1 - θ₂) ^ 2 < (1 - θ₁) ^ 2 := by nlinarith
  have hb : 0 ≤ (1 - θ₂) ^ 2 := sq_nonneg _
  nlinarith

lemma mono_share (θ₁ θ₂ c : ℝ) (h1 : 0 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ ≤ 1)
    (hx1 : 0 < 3 * θ₁ - c - 2 * c * θ₁) (hx2 : 0 < 3 * θ₂ - c - 2 * c * θ₂) (hc0 : 0 ≤ c) :
    ((3 * θ₂ - c - 2 * c * θ₂) ^ 2 + 8 * θ₂ * (1 - θ₂) ^ 2) /
        (3 * (3 * θ₂ - c - 2 * c * θ₂) ^ 2 + 8 * θ₂ * (1 - θ₂) ^ 2) <
      ((3 * θ₁ - c - 2 * c * θ₁) ^ 2 + 8 * θ₁ * (1 - θ₁) ^ 2) /
        (3 * (3 * θ₁ - c - 2 * c * θ₁) ^ 2 + 8 * θ₁ * (1 - θ₁) ^ 2) := by
  set a := 3 - 2 * c with ha
  have e1 : 3 * θ₁ - c - 2 * c * θ₁ = a * θ₁ - c := by rw [ha]; ring
  have e2 : 3 * θ₂ - c - 2 * c * θ₂ = a * θ₂ - c := by rw [ha]; ring
  rw [e1, e2] at *
  set x₁ := a * θ₁ - c with hx₁
  set x₂ := a * θ₂ - c with hx₂
  have hK1 : 0 < θ₁ * (1 - θ₁) ^ 2 := by
    have : 0 < 1 - θ₁ := by linarith
    positivity
  have hθ2 : 0 < θ₂ := by linarith
  have hK2 : 0 ≤ θ₂ * (1 - θ₂) ^ 2 := mul_nonneg hθ2.le (sq_nonneg _)
  have hx1p : 0 < x₁ := by rw [hx₁, ha]; linarith
  have hx2p : 0 < x₂ := by rw [hx₂, ha]; linarith
  have hx1s : 0 < x₁ ^ 2 := pow_pos hx1p 2
  have hx2s : 0 < x₂ ^ 2 := pow_pos hx2p 2
  -- key: θ₂ (1-θ₂)^2 x₁^2 < θ₁ (1-θ₁)^2 x₂^2
  have hA : θ₂ * x₁ ^ 2 ≤ θ₁ * x₂ ^ 2 := by
    have : θ₁ * x₂ ^ 2 - θ₂ * x₁ ^ 2 = (θ₂ - θ₁) * (a * θ₁ * (a * θ₂) - c ^ 2) := by
      rw [hx₁, hx₂]; ring
    have hp : 0 ≤ a * θ₁ * (a * θ₂) - c ^ 2 := by
      have h1' : c ≤ a * θ₁ := by linarith
      have h2' : c ≤ a * θ₂ := by linarith
      nlinarith [mul_le_mul h1' h2' hc0 (by linarith)]
    nlinarith
  have hB : (1 - θ₂) ^ 2 < (1 - θ₁) ^ 2 := by nlinarith
  have hkey : θ₂ * (1 - θ₂) ^ 2 * x₁ ^ 2 < θ₁ * (1 - θ₁) ^ 2 * x₂ ^ 2 := by
    have : θ₂ * x₁ ^ 2 * (1 - θ₂) ^ 2 < θ₁ * x₂ ^ 2 * (1 - θ₁) ^ 2 := by
      calc θ₂ * x₁ ^ 2 * (1 - θ₂) ^ 2 < θ₂ * x₁ ^ 2 * (1 - θ₁) ^ 2 :=
            mul_lt_mul_of_pos_left hB (mul_pos hθ2 hx1s)
        _ ≤ θ₁ * x₂ ^ 2 * (1 - θ₁) ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    linarith
  have hd2 : 0 < 3 * x₂ ^ 2 + 8 * θ₂ * (1 - θ₂) ^ 2 := by nlinarith
  have hd1 : 0 < 3 * x₁ ^ 2 + 8 * θ₁ * (1 - θ₁) ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ hd2 hd1]
  nlinarith

end BOGOPromo.NoStockpile.Cor4Aux

open BOGOPromo.NoStockpile BOGOPromo.NoStockpile.Cor4Aux

set_option maxHeartbeats 1000000 in
theorem solution (c : ℝ) (hc0 : 0 ≤ c) :
    (∀ θ : ℝ, 0 < θ → θ ≤ 1 → c < cBar θ →
      ∀ (wb : ℝ) (rb : ℝ → BPolicy) (wd : ℝ) (rd : ℝ → PPolicy) (wn : ℝ) (rn : ℝ → ℝ),
        IsEqB θ c wb rb → IsEqP θ c wd rd → IsEqN c wn rn →
        let πbm := (wb - c) * (rb wb).demand θ
        let πbr := (rb wb).profit θ wb
        let πdm := (wd - c) * (rd wd).demand θ
        let πdr := (rd wd).profit θ wd
        let πnm := (wn - c) * npDemand (rn wn)
        let πnr := npProfit wn (rn wn)
        -- part 1
        πbm = πdm ∧
        -- part 2
        (∃ pb pg pr pd : ℝ, rb wb = .bogo pb pg ∧ rd wd = .priceRed pr pd ∧ pb = pr ∧
          (θ < 1 → pg < pd)) ∧
        -- part 3
        πnr < πbr ∧ πnm + πnr < πbm + πbr ∧
        (θ < 1 → πdr < πbr ∧ πdm + πdr < πbm + πbr) ∧ (θ = 1 → πbr = πdr) ∧
        -- part 4
        (θ < 1 → πdr / (πdm + πdr) < πbr / (πbm + πbr) ∧
          πnr / (πnm + πnr) < πbr / (πbm + πbr))) ∧
    (∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ < θ₂ → θ₂ ≤ 1 → c < cBar θ₁ → c < cBar θ₂ →
      ∀ (wb₁ wd₁ wb₂ wd₂ : ℝ) (rb₁ rb₂ : ℝ → BPolicy) (rd₁ rd₂ : ℝ → PPolicy),
        IsEqB θ₁ c wb₁ rb₁ → IsEqP θ₁ c wd₁ rd₁ → IsEqB θ₂ c wb₂ rb₂ → IsEqP θ₂ c wd₂ rd₂ →
        -- part 2: the price gap p_d − p_g decreases in θ
        (rd₂ wd₂).promoPrice - (rb₂ wb₂).promoPrice <
          (rd₁ wd₁).promoPrice - (rb₁ wb₁).promoPrice ∧
        -- part 3: the retailer's BOGO advantage over PR decreases in θ
        (rb₂ wb₂).profit θ₂ wb₂ - (rd₂ wd₂).profit θ₂ wd₂ <
          (rb₁ wb₁).profit θ₁ wb₁ - (rd₁ wd₁).profit θ₁ wd₁ ∧
        -- part 4: the retailer's share of supply-chain profit under BOGO decreases in θ
        (rb₂ wb₂).profit θ₂ wb₂ / ((wb₂ - c) * (rb₂ wb₂).demand θ₂ + (rb₂ wb₂).profit θ₂ wb₂) <
          (rb₁ wb₁).profit θ₁ wb₁ / ((wb₁ - c) * (rb₁ wb₁).demand θ₁ + (rb₁ wb₁).profit θ₁ wb₁)) := by
  constructor
  · intro θ hθ0 hθ1 hc wb rb wd rd wn rn hb hd hn
    obtain ⟨hreg, _⟩ := region θ c hθ0 hθ1 hc0 hc
    have hcT : c < cTilde θ := lt_of_lt_of_le hc (cBar_le_cTilde θ hθ0 hθ1)
    have hc1 : c < 1 := by nlinarith
    obtain ⟨_, hbr, _, hbP, hbM⟩ := (proposition_2a θ c hθ0 hθ1 hc0 hcT).2 wb rb hb
    obtain ⟨_, hdr, _, hdP, hdM⟩ := (proposition_4a θ c hθ0 hθ1 hc0 hc).2 wd rd hd
    obtain ⟨_, _, _, hnP, hnM⟩ := (np_equilibrium c hc0 hc1).2 wn rn hn
    obtain ⟨P1, P2, P3, P4, P5, P6, _, _, _⟩ := pointwise θ c hθ0 hθ1 hc0 hreg
    intro πbm πbr πdm πdr πnm πnr
    simp only [πbm, πbr, πdm, πdr, πnm, πnr]
    rw [hbM, hbP, hdM, hdP, hnM, hnP]
    refine ⟨rfl, ⟨_, _, _, _, hbr, hdr, rfl, P6⟩, P1, by linarith, P3, P4, P5⟩
  · intro θ₁ θ₂ h1 h12 h2 hc1 hc2 wb₁ wd₁ wb₂ wd₂ rb₁ rb₂ rd₁ rd₂ hb₁ hd₁ hb₂ hd₂
    have h2' : 0 < θ₂ := by linarith
    obtain ⟨hreg1, hhalf1⟩ := region θ₁ c h1 (by linarith) hc0 hc1
    obtain ⟨hreg2, _⟩ := region θ₂ c h2' h2 hc0 hc2
    have hcT1 : c < cTilde θ₁ := lt_of_lt_of_le hc1 (cBar_le_cTilde θ₁ h1 (by linarith))
    have hcT2 : c < cTilde θ₂ := lt_of_lt_of_le hc2 (cBar_le_cTilde θ₂ h2' h2)
    obtain ⟨_, hbr1, _, hbP1, hbM1⟩ := (proposition_2a θ₁ c h1 (by linarith) hc0 hcT1).2 wb₁ rb₁ hb₁
    obtain ⟨_, hdr1, _, hdP1, _⟩ := (proposition_4a θ₁ c h1 (by linarith) hc0 hc1).2 wd₁ rd₁ hd₁
    obtain ⟨_, hbr2, _, hbP2, hbM2⟩ := (proposition_2a θ₂ c h2' h2 hc0 hcT2).2 wb₂ rb₂ hb₂
    obtain ⟨_, hdr2, _, hdP2, _⟩ := (proposition_4a θ₂ c h2' h2 hc0 hc2).2 wd₂ rd₂ hd₂
    obtain ⟨_, _, _, _, _, _, G1, A1, S1⟩ := pointwise θ₁ c h1 (by linarith) hc0 hreg1
    obtain ⟨_, _, _, _, _, _, G2, A2, S2⟩ := pointwise θ₂ c h2' h2 hc0 hreg2
    rw [hbM1, hbM2, hbP1, hbP2, hdP1, hdP2, S1, S2]
    refine ⟨?_, ?_, ?_⟩
    · rw [hbr1, hbr2, hdr1, hdr2]
      simp only [BPolicy.promoPrice, PPolicy.promoPrice]
      rw [G1, G2]
      exact mono_gap θ₁ θ₂ hhalf1 h12 h2
    · rw [A1, A2]
      exact mono_adv θ₁ θ₂ h1 h12 h2
    · have hx1 : 0 < 3 * θ₁ - c - 2 * c * θ₁ := by nlinarith
      have hx2 : 0 < 3 * θ₂ - c - 2 * c * θ₂ := by nlinarith
      exact mono_share θ₁ θ₂ c h1 h12 h2 hx1 hx2 hc0
