-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_singleton_right_jump_of_leftContinuousExtension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:03:25.434684+00:00
-- url     : https://prove2.me/submissions/b316f64d-7afd-4e08-adc0-8c64b38c7426

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_monotone_leftcontinuous_stieltjes_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω)
    (hleft : ∀ t : ℝ,
      ContinuousWithinAt (fun s : ℝ => D s.toNNReal ω) (Iic t) t)
    (t : ℝ) :
    dividendMeasure D ω {t} =
      ENNReal.ofReal
        (Function.rightLim (fun s : ℝ => D s.toNNReal ω) t -
          D t.toNNReal ω) := by
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro a b hab
    exact (hD.2.1 ω) (Real.toNNReal_mono hab)
  have hAtom :=
    monotone_leftcontinuous_stieltjes_atom
      (fun s : ℝ => D s.toNNReal ω) hmono hleft t
  unfold dividendMeasure
  rw [dif_pos hmono]
  exact hAtom
