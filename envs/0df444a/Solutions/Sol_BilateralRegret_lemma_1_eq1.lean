-- Prove2me | solution 1 for BilateralRegret.lemma_1_eq1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:13:55.168173+00:00
-- url     : https://prove2.me/submissions/dd247b92-764e-41bd-8383-8641bca4b9bb

import Mathlib
import Definitions.Def_BilateralRegret_GFT

set_option autoImplicit false

open MeasureTheory BilateralRegret

theorem solution (p s b : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    GFT p s b = (∫ l in Set.Icc p 1, ind (s ≤ p ∧ p ≤ l ∧ l ≤ b))
      + ∫ l in Set.Icc 0 p, ind (s ≤ l ∧ l ≤ p ∧ p ≤ b) := by
  by_cases h : s ≤ p ∧ p ≤ b
  · have e1 : (fun l => ind (s ≤ p ∧ p ≤ l ∧ l ≤ b)) =
        (Set.Icc p b).indicator (fun _ => (1 : ℝ)) := by
      funext l
      simp only [ind, Set.indicator, Set.mem_Icc, h.1, true_and]
    have e2 : (fun l => ind (s ≤ l ∧ l ≤ p ∧ p ≤ b)) =
        (Set.Icc s p).indicator (fun _ => (1 : ℝ)) := by
      funext l
      simp only [ind, Set.indicator, Set.mem_Icc, h.2, and_true]
    rw [e1, e2, integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl hb.2),
      Set.inter_eq_left.mpr (Set.Icc_subset_Icc hs.1 le_rfl),
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      Measure.real, Measure.real, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [h.2]), ENNReal.toReal_ofReal (by linarith [h.1])]
    simp only [GFT, ind, if_pos h]
    ring
  · have z1 : (fun l => ind (s ≤ p ∧ p ≤ l ∧ l ≤ b)) = fun _ => (0 : ℝ) := by
      funext l
      simp only [ind]
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1, h2.trans h3⟩
    have z2 : (fun l => ind (s ≤ l ∧ l ≤ p ∧ p ≤ b)) = fun _ => (0 : ℝ) := by
      funext l
      simp only [ind]
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1.trans h2, h3⟩
    rw [z1, z2, integral_zero, integral_zero]
    simp only [GFT, ind, if_neg h]
    ring
