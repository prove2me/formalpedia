-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_exponential_deficit_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:56:27.247794+00:00
-- url     : https://prove2.me/submissions/7546a96c-51ad-4d4e-8094-e9110224bf6b

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The Lévy exponential deficit detects infinite negative-jump intensity. -/
theorem solution
    (ν : Measure ℝ)
    (hsupport : ν (Ici (0 : ℝ)) = 0)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto
      (fun n : ℕ => ∫⁻ y, ENNReal.ofReal
        (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop (nhds (⊤ : ℝ≥0∞)) := by 
  set F : ℕ → ℝ → ℝ≥0∞ := fun n y => ENNReal.ofReal (1 - Real.exp ((n : ℝ) * y)) with hF
  have hmeas : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_const.sub
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
  have hpos0 : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y → F n y = 0 := by
    intro n y hy
    simp only [hF]
    apply ENNReal.ofReal_of_nonpos
    have : 0 ≤ (n : ℝ) * y := mul_nonneg (Nat.cast_nonneg _) hy
    linarith [Real.one_le_exp this]
  have hmonoF : Monotone F := by
    intro m n hmn y
    rcases lt_or_ge y 0 with hy | hy
    · simp only [hF]
      apply ENNReal.ofReal_le_ofReal
      have : (n : ℝ) * y ≤ (m : ℝ) * y :=
        mul_le_mul_of_nonpos_right (by exact_mod_cast hmn) hy.le
      linarith [Real.exp_le_exp.mpr this]
    · rw [hpos0 n y hy, hpos0 m y hy]
  have hsup : ∀ y : ℝ, y < 0 → ⨆ n, F n y = 1 := by
    intro y hy
    have hmono' : Monotone (fun n => F n y) := fun m n h => hmonoF h y
    have ht : Tendsto (fun n : ℕ => F n y) atTop (nhds (ENNReal.ofReal (1 - 0))) := by
      apply (ENNReal.continuous_ofReal.tendsto _).comp
      apply tendsto_const_nhds.sub
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hy
    rw [sub_zero, ENNReal.ofReal_one] at ht
    exact iSup_eq_of_tendsto hmono' ht
  have hlim : ∫⁻ y, ⨆ n, F n y ∂ν = ⊤ := by
    rw [eq_top_iff, ← hνinf, ← lintegral_indicator_one measurableSet_Iio]
    · apply lintegral_mono
      intro y
      by_cases hy : y < 0
      · rw [indicator_of_mem (by exact hy)]; simp only [hsup y hy, Pi.one_apply]; exact le_rfl
      · rw [indicator_of_notMem (by exact hy)]; exact zero_le
  have := tendsto_atTop_iSup (f := fun n => ∫⁻ y, F n y ∂ν)
    (fun m n h => lintegral_mono (hmonoF h))
  rw [← lintegral_iSup hmeas hmonoF, hlim] at this
  exact this
