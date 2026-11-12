-- Prove2me | solution 1 for CompetingKS.eq_17_18_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:53:14.516013+00:00
-- url     : https://prove2.me/submissions/b0739c5f-7f78-4d2d-98cb-4ac1f96cafd8

import Mathlib
import Definitions.Def_CompetingKS_unitOT

open CompetingKS in
theorem solution {η wi wj : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hwi : wi ∈ Set.Icc (0 : ℝ) 1) (hwj : wj ∈ Set.Icc (0 : ℝ) 1) :
    (1 - wi ≤ η / 2 * (1 - wj) →
      supplierOT 1 1 0 η wi wj = wj * ((1 - wj) / 2) ∧ retailerOT 1 1 η wi wj = 0) ∧
    (η / 2 * (1 - wj) < 1 - wi → η * (1 - wi) < 2 * (1 - wj) →
      supplierOT 1 1 0 η wi wj =
        wi * ((2 * (1 - wi) - η * (1 - wj)) / (4 - η ^ 2)) +
          wj * ((2 * (1 - wj) - η * (1 - wi)) / (4 - η ^ 2)) ∧
      retailerOT 1 1 η wi wj = (2 * (1 - wi) - η * (1 - wj)) ^ 2 / (4 - η ^ 2) ^ 2) ∧
    (2 * (1 - wj) ≤ η * (1 - wi) →
      supplierOT 1 1 0 η wi wj = wi * ((1 - wi) / 2) ∧
      retailerOT 1 1 η wi wj = (1 - wi) ^ 2 / 4) ∧
    disagreeOT 1 1 0 η wj = wj * ((1 - wj) / 2) := by
  obtain ⟨hwi0, hwi1⟩ := hwi
  obtain ⟨hwj0, hwj1⟩ := hwj
  have L0 : ∀ x y : ℝ, 2 * (1 - x) ≤ η * (1 - y) → qOT 1 1 η x y = 0 := by
    intro x y h
    unfold qOT
    rw [if_pos h]
  have L1 : ∀ x y : ℝ, ¬ (2 * (1 - x) ≤ η * (1 - y)) → 2 * (1 - y) ≤ η * (1 - x) →
      qOT 1 1 η x y = (1 - x) / 2 := by
    intro x y h h'
    unfold qOT
    rw [if_neg h, if_pos h', mul_one]
  have L2 : ∀ x y : ℝ, ¬ (2 * (1 - x) ≤ η * (1 - y)) → ¬ (2 * (1 - y) ≤ η * (1 - x)) →
      qOT 1 1 η x y = (2 * (1 - x) - η * (1 - y)) / (4 - η ^ 2) := by
    intro x y h h'
    unfold qOT
    rw [if_neg h, if_neg h', one_mul]
  have p1 : η * (1 - wj) ≤ 1 - wj := by nlinarith
  have p2 : η * (1 - wi) ≤ 1 - wi := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hA : 2 * (1 - wi) ≤ η * (1 - wj) := by linarith
    unfold supplierOT retailerOT ROT rOT priceOT price
    rw [L0 wi wj hA]
    by_cases hB : 2 * (1 - wj) ≤ η * (1 - wi)
    · have hj : wj = 1 := by linarith
      rw [L0 wj wi hB, hj]
      constructor <;> ring
    · rw [L1 wj wi hB hA]
      constructor <;> ring
  · intro h1 h2
    have hA : ¬ (2 * (1 - wi) ≤ η * (1 - wj)) := not_le.2 (by linarith)
    have hB : ¬ (2 * (1 - wj) ≤ η * (1 - wi)) := not_le.2 (by linarith)
    have hD : (0:ℝ) < 4 - η ^ 2 := by nlinarith
    have hD' : (4 - η ^ 2) ≠ 0 := hD.ne'
    unfold supplierOT retailerOT ROT rOT priceOT price
    rw [L2 wi wj hA hB, L2 wj wi hB hA]
    constructor
    · ring
    · field_simp <;> ring
  · intro hB
    unfold supplierOT retailerOT ROT rOT priceOT price
    by_cases hA : 2 * (1 - wi) ≤ η * (1 - wj)
    · have hi : wi = 1 := by linarith
      rw [L0 wi wj hA, L0 wj wi hB, hi]
      constructor <;> ring
    · rw [L1 wi wj hA hB, L0 wj wi hB]
      constructor <;> ring
  · unfold disagreeOT ROT
    by_cases hA : 2 * (1 - wj) ≤ η * (1 - (1 - η * (1 - wj) / 2))
    · have q1 : 0 ≤ η * ((1 - η) * (1 - wj)) :=
        mul_nonneg hη₀ (mul_nonneg (sub_nonneg.2 hη₁) (sub_nonneg.2 hwj1))
      have hj : wj = 1 := by nlinarith
      rw [L0 _ _ hA, hj]
      ring
    · have hB : 2 * (1 - (1 - η * (1 - wj) / 2)) ≤ η * (1 - wj) := by linarith
      rw [L1 _ _ hA hB]
      ring
