-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_open_interval_dividend_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:47:56.167969+00:00
-- url     : https://prove2.me/submissions/c3280baa-b10c-4bd3-a0c1-619c938bebe7

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict interval mass for the original left-continuous dividend strategy.
The left endpoint's right-payment atom and the right endpoint's right-payment
atom are both excluded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) :
    dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - rightLimit D a ω) := by
  let f : ℝ → ℝ := fun s => D s.toNNReal ω
  have hmono : Monotone f := by
    intro s t hst
    exact (hD.2.1 ω) (Real.toNNReal_mono hst)
  have hleft : ∀ t : ℝ, ContinuousWithinAt f (Iic t) t :=
    dividendStrategy_real_extension_leftContinuous D hD ω
  have hmeasure : dividendMeasure D ω = hmono.stieltjesFunction.measure := by
    unfold dividendMeasure
    rw [dif_pos hmono]
  have hLim (t : ℝ) :
      Function.leftLim (hmono.stieltjesFunction : ℝ → ℝ) t = f t := by
    change Function.leftLim (Function.rightLim f) t = f t
    rw [leftLim_rightLim (hmono.tendsto_leftLim t)]
    exact (hleft t).leftLim_eq
  have hright :
      (hmono.stieltjesFunction : ℝ → ℝ) (a : ℝ) =
        rightLimit D a ω := by
    change Function.rightLim (fun s : ℝ => D s.toNNReal ω) (a : ℝ) =
      rightLimit D a ω
    exact dividendPath_real_rightLim_eq_rightLimit D ω
      (fun s t hst => hD.2.1 ω hst) a
  rw [hmeasure, StieltjesFunction.measure_Ioo, hLim, hright]
  simp only [f, Real.toNNReal_coe]
