-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_scale_strictMonoOn_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:38:09.803432+00:00
-- url     : https://prove2.me/submissions/ae73fcb6-50b2-44ad-a2e2-f97de9ea014e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine q-scale function is strictly increasing at all positive
arguments under Standing, derived from Esscher-normalised monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    StrictMonoOn W (Ioi (0 : ℝ)) := by
  obtain ⟨hposW, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  intro x hx y hy hxy
  have hmono' :
      Real.exp (-φ * x) * W x ≤
        Real.exp (-φ * y) * W y :=
    hmono hx hy hxy.le
  have hexp : Real.exp (-φ * y) < Real.exp (-φ * x) := by
    apply Real.exp_lt_exp.mpr
    have hdiff : 0 < y - x := sub_pos.mpr hxy
    nlinarith [mul_pos hφ hdiff]
  by_contra hnot
  have hWle : W y ≤ W x := le_of_not_gt hnot
  have hmul1 :
      Real.exp (-φ * y) * W y ≤ Real.exp (-φ * y) * W x :=
    mul_le_mul_of_nonneg_left hWle (Real.exp_pos _).le
  have hmul2 :
      Real.exp (-φ * y) * W x < Real.exp (-φ * x) * W x :=
    mul_lt_mul_of_pos_right hexp (hposW x hx)
  exact (not_lt_of_ge hmono') (lt_of_le_of_lt hmul1 hmul2)
