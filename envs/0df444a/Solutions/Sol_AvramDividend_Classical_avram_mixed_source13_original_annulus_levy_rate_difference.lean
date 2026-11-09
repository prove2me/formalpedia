-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_annulus_levy_rate_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:16:55.540561+00:00
-- url     : https://prove2.me/submissions/8d3fc66b-fc86-4465-a4be-67bcf778ab78

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_rate_finite_n

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite cutoff Levy rates split into the lower cutoff and annulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    ((T : ℝ≥0∞) * X.ν (Iic d)).toReal =
      ((T : ℝ≥0∞) * X.ν (Iic c)).toReal +
      ((T : ℝ≥0∞) * X.ν (Ioc c d)).toReal := by
  classical
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  change ((T : ℝ≥0∞) * X.ν (Iic d)).toReal =
    ((T : ℝ≥0∞) * X.ν (Iic c)).toReal +
    ((T : ℝ≥0∞) * X.ν (Ioc c d)).toReal
  have hcd : c ≤ d := by
    dsimp [c, d]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnmR : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have hNat : n + 1 ≤ m + 1 := by omega
      exact_mod_cast hNat
    have hrec : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hn hnmR
    linarith
  have hdis : Disjoint (Iic c) (Ioc c d) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx) hy.1
  have hunion : Iic d = Iic c ∪ Ioc c d := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      by_cases hxc : x ≤ c
      · exact Or.inl hxc
      · exact Or.inr ⟨lt_of_not_ge hxc, hx⟩
    · rintro (hLeft | hRight)
      · exact le_trans hLeft hcd
      · exact hRight.2
  have hMeasure : X.ν (Iic d) =
      X.ν (Iic c) + X.ν (Ioc c d) := by
    rw [hunion]
    exact measure_union hdis measurableSet_Ioc
  have hνn : X.ν (Iic c) < ⊤ := by
    simpa only [c] using
      (avram_p2_e_compensator_original_negative_band_rate_finite_n X n)
  have hνm : X.ν (Iic d) < ⊤ := by
    simpa only [d] using
      (avram_p2_e_compensator_original_negative_band_rate_finite_n X m)
  have hνA : X.ν (Ioc c d) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (by
      intro x hx
      exact hx.2)) hνm
  have hN : ((T : ℝ≥0∞) * X.ν (Iic c)) ≠ ⊤ := by
    exact ne_of_lt (ENNReal.mul_lt_top (by simp) hνn)
  have hA : ((T : ℝ≥0∞) * X.ν (Ioc c d)) ≠ ⊤ := by
    exact ne_of_lt (ENNReal.mul_lt_top (by simp) hνA)
  have hSplit : ((T : ℝ≥0∞) * X.ν (Iic d)) =
      (T : ℝ≥0∞) * X.ν (Iic c) +
      (T : ℝ≥0∞) * X.ν (Ioc c d) := by
    rw [hMeasure, mul_add]
  have hReal := congrArg ENNReal.toReal hSplit
  rw [ENNReal.toReal_add hN hA] at hReal
  exact hReal
