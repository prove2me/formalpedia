-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_positive_indicator_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:48:09.561099+00:00
-- url     : https://prove2.me/submissions/f971caaa-7f3f-4133-b8f9-93dee5197e0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    Continuous ((Ioi (0 : ℝ)).indicator V) := by
  have hz : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing
      X q hq W hW hσ
  have hc : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hz
  have hfun :
      ((Ioi (0 : ℝ)).indicator V) =
        (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
    funext x
    by_cases hx : 0 < x
    · have hxmem : x ∈ Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxmem]
      exact hV x hx
    · have hxmem : x ∉ Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_notMem hxmem]
      have hzero : W x = 0 := by
        rcases lt_or_eq_of_le (le_of_not_gt hx) with hneg | heq
        · exact hW.1 x hneg
        · simpa [heq] using hz
      simp [hzero]
  rw [hfun]
  exact (Real.continuous_exp.comp (by fun_prop)).mul hc
