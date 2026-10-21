-- Prove2me | solution 1 for FirstPriceLearning.NonIID.posterior_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:53:55.832992+00:00
-- url     : https://prove2.me/submissions/ae5da9f2-1ce8-4015-8d94-e19fc19ec22c

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

set_option autoImplicit false
open MeasureTheory

theorem solution (v b : ℝ) (hv : 1 / 4 ≤ v) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∫ m, FirstPriceLearning.Stochastic.payoff v b m ∂((2 : ENNReal)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac (1 / 8 : ℝ))) ≤
        ⨆ b' : Set.Icc (0 : ℝ) 1,
          (v - (b' : ℝ)) / 2 * (1 + (if (1 / 8 : ℝ) ≤ (b' : ℝ) then 1 else 0)) ∧
      (⨆ b' : Set.Icc (0 : ℝ) 1,
          (v - (b' : ℝ)) / 2 * (1 + (if (1 / 8 : ℝ) ≤ (b' : ℝ) then 1 else 0))) =
        max (v / 2) (v - 1 / 8) ∧
      max (v / 2) (v - 1 / 8) = v - 1 / 8 := by
  set g : Set.Icc (0 : ℝ) 1 → ℝ := fun b' =>
    (v - (b' : ℝ)) / 2 * (1 + (if (1 / 8 : ℝ) ≤ (b' : ℝ) then 1 else 0)) with hg
  have hbound : ∀ b' : Set.Icc (0 : ℝ) 1, g b' ≤ max (v / 2) (v - 1 / 8) := by
    intro b'
    have h0 := b'.2.1
    simp only [hg]
    by_cases h : (1 / 8 : ℝ) ≤ (b' : ℝ)
    · rw [if_pos h]
      refine le_trans ?_ (le_max_right _ _)
      linarith
    · rw [if_neg h]
      refine le_trans ?_ (le_max_left _ _)
      linarith
  have hbdd : BddAbove (Set.range g) := ⟨_, by rintro _ ⟨b', rfl⟩; exact hbound b'⟩
  have hsup : (⨆ b' : Set.Icc (0 : ℝ) 1, g b') = max (v / 2) (v - 1 / 8) := by
    apply le_antisymm (ciSup_le hbound)
    apply max_le
    · refine le_trans ?_ (le_ciSup hbdd ⟨0, by simp⟩)
      simp only [hg]
      rw [if_neg (by norm_num)]
      norm_num
    · refine le_trans ?_ (le_ciSup hbdd ⟨1 / 8, by norm_num⟩)
      simp only [hg]
      rw [if_pos le_rfl]
      norm_num
  have hmax : max (v / 2) (v - 1 / 8) = v - 1 / 8 := by
    apply max_eq_right
    linarith
  have hint : ∫ m, FirstPriceLearning.Stochastic.payoff v b m ∂((2 : ENNReal)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac (1 / 8 : ℝ))) = g ⟨b, hb⟩ := by
    rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
      integral_dirac, integral_dirac]
    simp only [hg, FirstPriceLearning.Stochastic.payoff]
    have h0 := hb.1
    rw [if_pos h0]
    by_cases h : (1 / 8 : ℝ) ≤ b
    · simp only [if_pos h]
      norm_num
      ring
    · simp only [if_neg h]
      norm_num
      ring
  refine ⟨?_, hsup, hmax⟩
  rw [hint]
  exact le_ciSup hbdd ⟨b, hb⟩
