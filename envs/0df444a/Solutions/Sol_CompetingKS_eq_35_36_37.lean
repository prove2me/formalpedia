-- Prove2me | solution 1 for CompetingKS.eq_35_36_37
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:39:05.957522+00:00
-- url     : https://prove2.me/submissions/5a90d436-b064-43cf-b346-7aa369c70149

import Mathlib
import Definitions.Def_CompetingKS_unitOT

open CompetingKS in
theorem solution {η wi wj : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1)
    (hwi : wi ∈ Set.Icc (0 : ℝ) 1) (hwj : wj ∈ Set.Icc (0 : ℝ) 1) :
    (1 - wi ≤ η * (1 - wj) →
      supplierTO 1 1 0 η wi wj = 0 ∧ retailerTO 1 1 η wi wj = (1 - wj) ^ 2 / 4) ∧
    (η * (1 - wj) < 1 - wi → η * (1 - wi) < 1 - wj →
      supplierTO 1 1 0 η wi wj = wi * (((1 - wi) - η * (1 - wj)) / (2 * (1 - η ^ 2))) ∧
      retailerTO 1 1 η wi wj =
        ((1 - wi) * ((1 - wi) - η * (1 - wj)) + (1 - wj) * ((1 - wj) - η * (1 - wi))) /
          (4 * (1 - η ^ 2))) ∧
    (1 - wj ≤ η * (1 - wi) →
      supplierTO 1 1 0 η wi wj = wi * ((1 - wi) / 2) ∧
      retailerTO 1 1 η wi wj = (1 - wi) ^ 2 / 4) ∧
    disagreeTO 1 1 η wj = (1 - wj) ^ 2 / 4 := by
  obtain ⟨hwi0, hwi1⟩ := hwi
  obtain ⟨hwj0, hwj1⟩ := hwj
  have q1 : ∀ x y : ℝ, 1 - x ≤ η * (1 - y) → qTO 1 1 η x y = 0 := by
    intro x y h
    unfold qTO
    rw [if_pos h]
  have q2 : ∀ x y : ℝ, ¬ (1 - x ≤ η * (1 - y)) → 1 - y ≤ η * (1 - x) →
      qTO 1 1 η x y = (1 - x) / (2 * 1) := by
    intro x y h h'
    unfold qTO
    rw [if_neg h, if_pos h']
  have q3 : ∀ x y : ℝ, ¬ (1 - x ≤ η * (1 - y)) → ¬ (1 - y ≤ η * (1 - x)) →
      qTO 1 1 η x y = ((1 - x) - η * (1 - y)) / (2 * 1 * (1 - η ^ 2)) := by
    intro x y h h'
    unfold qTO
    rw [if_neg h, if_neg h']
  have hD : 0 < 1 - η ^ 2 := by nlinarith
  -- if both thresholds hold, both prices are 1
  have both : ∀ x y : ℝ, x ≤ 1 → y ≤ 1 → 1 - x ≤ η * (1 - y) → 1 - y ≤ η * (1 - x) →
      x = 1 ∧ y = 1 := by
    intro x y hx hy h h'
    have e1 : (1 - y) * (1 - η ^ 2) ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left h hη₀]
    have e2 : (1 - x) * (1 - η ^ 2) ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left h' hη₀]
    have hy' : 1 - y ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hc hD
      linarith
    have hx' : 1 - x ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hc hD
      linarith
    constructor <;> linarith
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h3 => ?_, ?_⟩
  · unfold supplierTO RTO retailerTO rTO priceTO price
    rw [q1 wi wj h]
    by_cases hj : 1 - wj ≤ η * (1 - wi)
    · obtain ⟨hi1, hj1⟩ := both wi wj hwi1 hwj1 h hj
      rw [q1 wj wi hj]
      subst hi1
      subst hj1
      constructor <;> ring
    · rw [q2 wj wi hj h]
      constructor <;> ring
  · have hn1 : ¬ (1 - wi ≤ η * (1 - wj)) := not_le.mpr h1
    have hn2 : ¬ (1 - wj ≤ η * (1 - wi)) := not_le.mpr h2
    unfold supplierTO RTO retailerTO rTO priceTO price
    rw [q3 wi wj hn1 hn2, q3 wj wi hn2 hn1]
    have hD0 : 1 - η ^ 2 ≠ 0 := hD.ne'
    constructor
    · ring
    · field_simp <;> ring
  · unfold supplierTO RTO retailerTO rTO priceTO price
    by_cases hi : 1 - wi ≤ η * (1 - wj)
    · obtain ⟨hi1, hj1⟩ := both wi wj hwi1 hwj1 hi h3
      rw [q1 wi wj hi, q1 wj wi h3]
      subst hi1
      subst hj1
      constructor <;> ring
    · rw [q2 wi wj hi h3, q1 wj wi h3]
      constructor <;> ring
  · unfold disagreeTO rTO priceTO price
    by_cases hb : 1 - wj ≤ η * (1 - (1 - η * (1 - wj)))
    · have hb' : 1 - (1 - η * (1 - wj)) ≤ η * (1 - wj) := by linarith
      have hle : 1 - η * (1 - wj) ≤ 1 := by nlinarith [mul_nonneg hη₀ (sub_nonneg.mpr hwj1)]
      obtain ⟨hj1, _⟩ := both wj (1 - η * (1 - wj)) hwj1 hle hb hb'
      rw [q1 wj _ hb]
      subst hj1
      ring
    · have hb' : 1 - (1 - η * (1 - wj)) ≤ η * (1 - wj) := by linarith
      rw [q2 wj _ hb hb', q1 _ wj hb']
      ring
