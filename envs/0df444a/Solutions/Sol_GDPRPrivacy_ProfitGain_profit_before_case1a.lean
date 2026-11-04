-- Prove2me | solution 1 for GDPRPrivacy.ProfitGain.profit_before_case1a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:11:32.617465+00:00
-- url     : https://prove2.me/submissions/65a64db8-517a-4ebd-98ce-0ef759de8f3e

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
import Theorems.Thm_GDPRPrivacy_PriceRise_eq4_demand_before
import Theorems.Thm_GDPRPrivacy_PriceRise_eq5_demand_in
import Theorems.Thm_GDPRPrivacy_PriceRise_eq6_demand_out

set_option autoImplicit false
open MeasureTheory GDPRPrivacy.PriceRise

namespace GDPR2Core

theorem dB_nonneg (x p : ℝ) : 0 ≤ demandBefore x p := ENNReal.toReal_nonneg
theorem dIn_nonneg (x p : ℝ) : 0 ≤ demandIn x p := ENNReal.toReal_nonneg
theorem dOut_nonneg (x p : ℝ) : 0 ≤ demandOut x p := ENNReal.toReal_nonneg

theorem pt_null : volume ({((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) = 0 := measure_singleton _

theorem dB_zero (x p : ℝ) (h : 1 + x ≤ p) : demandBefore x p = 0 := by
  unfold demandBefore
  have hs : buyersBefore x p ⊆ {((1 : ℝ), (0 : ℝ))} := by
    rintro ⟨v, c⟩ ⟨⟨⟨hv0, hv1⟩, ⟨hc0, hc1⟩⟩, hu⟩
    simp only [utilS] at hu
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]
    constructor <;> linarith
  rw [measure_mono_null hs pt_null, ENNReal.toReal_zero]

theorem dIn_zero (x p : ℝ) (h : 1 + x ≤ p) : demandIn x p = 0 := by
  unfold demandIn
  have hs : optInSet x p ⊆ {((1 : ℝ), (0 : ℝ))} := by
    rintro ⟨v, c⟩ ⟨⟨⟨hv0, hv1⟩, ⟨hc0, hc1⟩⟩, hu, _⟩
    simp only at hu
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]
    constructor <;> linarith
  rw [measure_mono_null hs pt_null, ENNReal.toReal_zero]

theorem dOut_zero (x p : ℝ) (h : 1 < p) : demandOut x p = 0 := by
  unfold demandOut
  have hs : optOutSet x p = ∅ := by
    ext ⟨v, c⟩
    simp only [optOutSet, typeSquare, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨_, hv1⟩, _⟩, hp, _⟩
    linarith
  rw [hs, measure_empty, ENNReal.toReal_zero]

theorem dIn_le (x p : ℝ) (hx : 0 ≤ x) : demandIn x p ≤ x := by
  unfold demandIn
  have hs : optInSet x p ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) x := by
    rintro ⟨v, c⟩ ⟨⟨hv, ⟨hc0, _⟩⟩, _, hcx⟩
    exact ⟨hv, hc0, hcx⟩
  have hv : volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) x) = ENNReal.ofReal x := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    simp
  have hle := measure_mono (μ := volume) hs
  rw [hv] at hle
  calc (volume (optInSet x p)).toReal ≤ (ENNReal.ofReal x).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = x := ENNReal.toReal_ofReal hx

/-- Before the GDPR, case 1a. -/
theorem before_core (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < (1 - 2 * x) / 2) :
    profitBefore x α ((1 + x - 2 * α) / 3) = 2 * (1 + x + α) ^ 3 / 27 ∧
    (∀ p, profitBefore x α p ≤ 2 * (1 + x + α) ^ 3 / 27) ∧
    (∀ p, (p ≤ x ∨ 1 + x ≤ p) → profitBefore x α p < 2 * (1 + x + α) ^ 3 / 27) := by
  have hM : 0 < 2 * (1 + x + α) ^ 3 / 27 := by positivity
  -- value of the case-1a branch
  have g_le : ∀ p, x < p → p < 1 + x →
      profitBefore x α p = (p + α) * ((1 + x - p) ^ 2 / 2) := by
    intro p h1 h2
    unfold profitBefore
    rw [((eq4_demand_before x p hx0 hx1).1 h1 h2)]
  -- key inequality for the cubic, valid when 1 + x - p ≥ 0
  have cubic : ∀ p, p ≤ 1 + x → (p + α) * ((1 + x - p) ^ 2 / 2) =
      2 * (1 + x + α) ^ 3 / 27 - (3 * (1 + x - p) - 2 * (1 + x + α)) ^ 2 *
        (3 * (1 + x - p) + (1 + x + α)) / 54 := by
    intro p _; ring
  -- strict bound at p ≤ x
  have low : ∀ p, p ≤ x → profitBefore x α p < 2 * (1 + x + α) ^ 3 / 27 := by
    intro p hp
    by_cases hpa : p + α ≤ 0
    · unfold profitBefore
      have := dB_nonneg x p
      nlinarith
    · push Not at hpa
      have hp1 : x - 1 ≤ p := by linarith
      unfold profitBefore
      rw [(eq4_demand_before x p hx0 hx1).2 hp1 hp]
      -- f(p) ≤ f(x) = (x+α)/2 < M
      have h1 : (p + α) * (1 - (1 - x + p) ^ 2 / 2) ≤ (x + α) / 2 := by
        set u := x - p with hu
        have hu0 : 0 ≤ u := by linarith
        have hw : u ≤ x + α := by linarith
        have e : (p + α) * (1 - (1 - x + p) ^ 2 / 2) = (x + α - u) * (1 - (1 - u) ^ 2 / 2) := by
          rw [hu]; ring
        rw [e]
        have : (x + α - u) * (1 - u / 2) ≤ 1 / 2 := by nlinarith
        nlinarith
      have h2 : (x + α) / 2 < 2 * (1 + x + α) ^ 3 / 27 := by
        have e := cubic x (by linarith)
        have e2 : (x + α) * ((1 + x - x) ^ 2 / 2) = (x + α) / 2 := by ring
        rw [e2] at e
        rw [e]
        have : 0 < (3 * (1 + x - x) - 2 * (1 + x + α)) ^ 2 := by
          have : 3 * (1 + x - x) - 2 * (1 + x + α) ≠ 0 := by intro h; linarith
          positivity
        have : 0 < 3 * (1 + x - x) + (1 + x + α) := by linarith
        nlinarith
      linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [g_le _ (by linarith) (by linarith)]; ring
  · intro p
    rcases le_or_gt p x with hp | hp
    · exact (low p hp).le
    rcases lt_or_ge p (1 + x) with hp2 | hp2
    · rw [g_le p hp hp2, cubic p hp2.le]
      have : 0 ≤ (3 * (1 + x - p) - 2 * (1 + x + α)) ^ 2 := sq_nonneg _
      have : 0 ≤ 3 * (1 + x - p) + (1 + x + α) := by linarith
      nlinarith
    · unfold profitBefore; rw [dB_zero x p hp2]; linarith
  · rintro p (hp | hp)
    · exact low p hp
    · unfold profitBefore; rw [dB_zero x p hp]; linarith

/-- After the GDPR, case 2a. -/
theorem after_core (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα2 : 2 * α * x < 2 - 4 * x + x ^ 2) :
    profitAfter x α ((2 * (1 - α * x) + x ^ 2) / 4) =
        (4 + 4 * x * (x + 2 * α + 2 * α * x) + x ^ 2 * (x - 2 * α) ^ 2) / 16 ∧
    (∀ p, profitAfter x α p ≤
        (4 + 4 * x * (x + 2 * α + 2 * α * x) + x ^ 2 * (x - 2 * α) ^ 2) / 16) ∧
    (∀ p, (p ≤ x ∨ 1 + x ≤ p) → profitAfter x α p <
        (4 + 4 * x * (x + 2 * α + 2 * α * x) + x ^ 2 * (x - 2 * α) ^ 2) / 16) := by
  set M := (4 + 4 * x * (x + 2 * α + 2 * α * x) + x ^ 2 * (x - 2 * α) ^ 2) / 16 with hMdef
  set ps := (2 * (1 - α * x) + x ^ 2) / 4 with hps
  have hps1 : x < ps := by rw [hps]; nlinarith
  have hps2 : ps ≤ 1 := by rw [hps]; nlinarith
  -- middle branch: x < p ≤ 1
  have mid : ∀ p, x < p → p ≤ 1 → profitAfter x α p = M - (p - ps) ^ 2 := by
    intro p h1 h2
    unfold profitAfter demandAfter
    rw [(eq5_demand_in x p hx0 hx1).2.1 h1 h2, (eq6_demand_out x p hx0 hx1).2 (by linarith) h2,
      hMdef, hps]
    ring
  have hMpos : 0 < M := by
    have := mid ps hps1 hps2
    have h0 : 0 < profitAfter x α ps := by
      unfold profitAfter demandAfter
      rw [(eq5_demand_in x ps hx0 hx1).2.1 hps1 hps2,
        (eq6_demand_out x ps hx0 hx1).2 (by linarith) hps2]
      have : 0 ≤ (1 - x) * (1 - ps) := mul_nonneg (by linarith) (by linarith)
      have : 0 < x ^ 2 / 2 + x * (1 - ps) := by nlinarith
      have : 0 < ps := by linarith
      nlinarith
    rw [this] at h0; nlinarith
  have hfx : profitAfter x α x < M := by
    -- value at x via the left branch equals the middle polynomial at x
    have e : profitAfter x α x = M - (x - ps) ^ 2 := by
      unfold profitAfter demandAfter
      rw [(eq5_demand_in x x hx0 hx1).2.2 hx0.le le_rfl,
        (eq6_demand_out x x hx0 hx1).2 hx0.le hx1.le, hMdef, hps]
      ring
    rw [e]
    have : 0 < (x - ps) ^ 2 := by
      have : x - ps ≠ 0 := by intro h; linarith
      positivity
    linarith
  have low : ∀ p, p ≤ x → profitAfter x α p < M := by
    intro p hp
    rcases lt_or_ge p 0 with hp0 | hp0
    · -- p < 0
      have h1 : profitAfter x α p ≤ α * x := by
        unfold profitAfter demandAfter
        have a1 := dIn_nonneg x p
        have a2 := dOut_nonneg x p
        have a3 := dIn_le x p hx0.le
        nlinarith
      have h2 : profitAfter x α 0 = α * x := by
        unfold profitAfter demandAfter
        rw [(eq5_demand_in x 0 hx0 hx1).2.2 le_rfl hx0.le]
        ring
      have h3 : profitAfter x α 0 ≤ profitAfter x α x := by
        unfold profitAfter demandAfter
        rw [(eq5_demand_in x 0 hx0 hx1).2.2 le_rfl hx0.le,
          (eq5_demand_in x x hx0 hx1).2.2 hx0.le le_rfl,
          (eq6_demand_out x 0 hx0 hx1).2 le_rfl (by linarith),
          (eq6_demand_out x x hx0 hx1).2 hx0.le hx1.le]
        nlinarith
      linarith
    · have h1 : profitAfter x α p ≤ profitAfter x α x := by
        unfold profitAfter demandAfter
        rw [(eq5_demand_in x p hx0 hx1).2.2 hp0 hp,
          (eq5_demand_in x x hx0 hx1).2.2 hx0.le le_rfl,
          (eq6_demand_out x p hx0 hx1).2 hp0 (by linarith),
          (eq6_demand_out x x hx0 hx1).2 hx0.le hx1.le]
        set Q := (2 - 2 * x + x ^ 2 - 2 * p + p * x - p ^ 2 - α * (p + x)) / 2 with hQ
        have hQ0 : 0 ≤ Q := by
          have hQx : 0 ≤ (2 - 2 * x + x ^ 2 - 2 * x + x * x - x ^ 2 - α * (x + x)) := by nlinarith
          have hQ0' : 0 ≤ (2 - 2 * x + x ^ 2 - α * x) := by nlinarith
          have key : x * (2 - 2 * x + x ^ 2 - 2 * p + p * x - p ^ 2 - α * (p + x)) =
              (x - p) * (2 - 2 * x + x ^ 2 - α * x) +
              p * (2 - 2 * x + x ^ 2 - 2 * x + x * x - x ^ 2 - α * (x + x)) + x * p * (x - p) := by
            ring
          have : 0 ≤ x * (2 - 2 * x + x ^ 2 - 2 * p + p * x - p ^ 2 - α * (p + x)) := by
            rw [key]
            have : 0 ≤ x - p := by linarith
            have := mul_nonneg this hQ0'
            have := mul_nonneg hp0 hQx
            have := mul_nonneg (mul_nonneg hx0.le hp0) (by linarith : (0:ℝ) ≤ x - p)
            linarith
          rw [hQ]
          have := (mul_nonneg_iff_of_pos_left hx0).1 this
          linarith
        have e : (x * (x - x ^ 2 / 2 + (1 - x) * (1 - x)) + α * (x - x ^ 2 / 2)) -
            (p * (p ^ 2 / 2 * (-1) + x + (1 - x) * (1 - p)) + α * (x - p ^ 2 / 2)) =
            (x - p) * Q := by rw [hQ]; ring
        have : 0 ≤ (x - p) * Q := mul_nonneg (by linarith) hQ0
        nlinarith
      linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [mid ps hps1 hps2]; ring
  · intro p
    rcases le_or_gt p x with hp | hp
    · exact (low p hp).le
    rcases le_or_gt p 1 with hp1 | hp1
    · rw [mid p hp hp1]; nlinarith [sq_nonneg (p - ps)]
    rcases lt_or_ge p (1 + x) with hp2 | hp2
    · have e1 : profitAfter x α 1 ≤ M := by
        rw [mid 1 (by linarith) le_rfl]; nlinarith [sq_nonneg (1 - ps)]
      have e2 : profitAfter x α p ≤ profitAfter x α 1 := by
        rw [mid 1 (by linarith) le_rfl]
        unfold profitAfter demandAfter
        rw [(eq5_demand_in x p hx0 hx1).1 hp1 hp2, dOut_zero x p hp1]
        rw [← mid 1 (by linarith) le_rfl]
        unfold profitAfter demandAfter
        rw [(eq5_demand_in x 1 hx0 hx1).2.1 hx1 le_rfl, (eq6_demand_out x 1 hx0 hx1).2 zero_le_one le_rfl]
        set t := 1 + x - p with ht
        have ht0 : 0 < t := by linarith
        have htx : t < x := by linarith
        have e : (1 + α) * x ^ 2 - (1 + x + α - t) * t ^ 2 =
            (x - t) * ((1 + α) * (x + t) - t ^ 2) := by ring
        have h3 : 0 ≤ (x - t) * ((1 + α) * (x + t) - t ^ 2) :=
          mul_nonneg (by linarith) (by nlinarith)
        have hp' : p = 1 + x - t := by rw [ht]; ring
        rw [hp']
        nlinarith
      linarith
    · unfold profitAfter demandAfter
      rw [dIn_zero x p hp2, dOut_zero x p (by linarith)]
      linarith
  · rintro p (hp | hp)
    · exact low p hp
    · unfold profitAfter demandAfter
      rw [dIn_zero x p hp, dOut_zero x p (by linarith)]
      linarith

end GDPR2Core

theorem GDPR2Core.of_alpha1 (x α : ℝ) (hα : 0 ≤ α) (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    α < (1 - 2 * x) / 2 := by
  unfold GDPRPrivacy.PriceRise.alpha1 at hα1
  rcases le_total ((1 - 2 * x) / 2) 0 with h | h
  · rw [max_eq_right h] at hα1; linarith
  · rwa [max_eq_left h] at hα1

theorem GDPR2Core.of_alpha2 (x α : ℝ) (hx0 : 0 < x) (hα : 0 ≤ α)
    (hα2 : α < GDPRPrivacy.PriceRise.alpha2 x) : 2 * α * x < 2 - 4 * x + x ^ 2 := by
  unfold GDPRPrivacy.PriceRise.alpha2 at hα2
  rcases le_total ((2 - 4 * x + x ^ 2) / (2 * x)) 0 with h | h
  · rw [max_eq_right h] at hα2; linarith
  · rw [max_eq_left h, lt_div_iff₀ (by positivity)] at hα2; linarith

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    ∀ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p →
      GDPRPrivacy.PriceRise.profitBefore x α p = 2 * (1 + x + α) ^ 3 / 27 := by
  obtain ⟨hv, hb, -⟩ := GDPR2Core.before_core x α hx0 hx1 hα (GDPR2Core.of_alpha1 x α hα hα1)
  refine ⟨⟨(1 + x - 2 * α) / 3, fun p _ => by rw [hv]; exact hb p⟩, fun p hp => ?_⟩
  have : profitBefore x α ((1 + x - 2 * α) / 3) ≤ profitBefore x α p := hp (Set.mem_univ ((1 + x - 2 * α) / 3))
  rw [hv] at this
  exact le_antisymm (hb p) this
