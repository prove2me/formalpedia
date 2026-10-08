-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividendMeasure_Ico_ge_end_weighted_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:26:35.344007+00:00
-- url     : https://prove2.me/submissions/f1bd287f-e3f9-4fce-8142-f5844f8adb12

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_eq_dividend_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ))) *
      (D b ω - D a ω)) ≤
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  have hpoint (s : ℝ) (hs : s ∈ Ico (a : ℝ) (b : ℝ)) :
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(q * s))) := by
    have hmul : q * s ≤ q * (b : ℝ) :=
      mul_le_mul_of_nonneg_left hs.2.le hq
    have he : Real.exp (-(q * (b : ℝ))) ≤ Real.exp (-(q * s)) :=
      Real.exp_le_exp.mpr (neg_le_neg hmul)
    exact ENNReal.ofReal_le_ofReal he
  calc
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ))) *
      (D b ω - D a ω)) =
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (D b ω - D a ω) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) := by
      rw [dividendMeasure_Ico_eq_dividend_increment D hD ω a b]
    _ = ∫⁻ _s in Ico (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * (b : ℝ))))
          ∂(dividendMeasure D ω) := by simp
    _ ≤ ∫⁻ s in Ico (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) := by
      exact lintegral_mono_ae
        (ae_restrict_of_forall_mem measurableSet_Ico hpoint)
