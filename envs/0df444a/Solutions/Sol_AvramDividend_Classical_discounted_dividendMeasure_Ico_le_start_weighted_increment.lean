-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividendMeasure_Ico_le_start_weighted_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:20:58.212993+00:00
-- url     : https://prove2.me/submissions/82c147ce-df72-4298-9cad-3dfd155d1e49

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
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ))) *
        (D b ω - D a ω)) := by
  have hpoint (s : ℝ) (hs : s ∈ Ico (a : ℝ) (b : ℝ)) :
      ENNReal.ofReal (Real.exp (-(q * s))) ≤
        ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) := by
    have hmul : q * (a : ℝ) ≤ q * s :=
      mul_le_mul_of_nonneg_left hs.1 hq
    have he : Real.exp (-(q * s)) ≤ Real.exp (-(q * (a : ℝ))) :=
      Real.exp_le_exp.mpr (neg_le_neg hmul)
    exact ENNReal.ofReal_le_ofReal he
  calc
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ∫⁻ _s in Ico (a : ℝ) (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * (a : ℝ))))
            ∂(dividendMeasure D ω) := by
      exact lintegral_mono_ae
        (ae_restrict_of_forall_mem measurableSet_Ico hpoint)
    _ = ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) := by simp
    _ = ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal (D b ω - D a ω) := by
      rw [dividendMeasure_Ico_eq_dividend_increment D hD ω a b]
    _ = ENNReal.ofReal (Real.exp (-(q * (a : ℝ))) *
        (D b ω - D a ω)) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
