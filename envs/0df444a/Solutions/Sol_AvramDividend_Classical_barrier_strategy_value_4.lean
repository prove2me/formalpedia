-- Prove2me | solution 4 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:51:31.628841+00:00
-- url     : https://prove2.me/submissions/d4017301-2827-475d-8f03-ad9b0b09f85c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact published barrier_strategy_value statement. Converts the
    two stochastic factor identities into W(x)/W'(a), proving W(a)>0
    from C¹ regularity, nonnegativity at zero and strictly positive
    derivative via the mean-value theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / deriv W a) := by
  have hderpos := scaleDeriv_pos X hX q hq W hW
  have hda : 0 < deriv W a := hderpos a ha
  have hcont : ContinuousOn W (Icc 0 a) := by
    apply hW.2.2.1.mono
    intro z hz
    exact hz.1
  have hdiff : DifferentiableOn ℝ W (Ioo 0 a) := by
    apply (scaleFunction_contDiff_one X hX q hq W hW).differentiableOn_one.mono
    intro z hz
    exact hz.1
  obtain ⟨z, hz, hmean⟩ :=
    exists_deriv_eq_slope W ha hcont hdiff
  have hquot : 0 < (W a - W 0) / (a - 0) := by
    rw [← hmean]
    exact hderpos z hz.1
  have hdiffpos : 0 < W a - W 0 := by
    have ha0 : 0 < a - 0 := by simpa using ha
    have h := (lt_div_iff₀ ha0).1 hquot
    simpa using h
  have hWa : 0 < W a := by
    have hW0 : 0 ≤ W 0 := hW.2.1 0 le_rfl
    linarith
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hratio : 0 ≤ W x / W a := div_nonneg hWx hWa.le
  calc
    dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
      barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa
    _ = ENNReal.ofReal (W x / W a) *
          ENNReal.ofReal (W a / deriv W a) := by
      rw [barrierSupValue_eq_scale_ratio X hX q hq W hW a ha]
    _ = ENNReal.ofReal ((W x / W a) * (W a / deriv W a)) := by
      rw [ENNReal.ofReal_mul hratio]
    _ = ENNReal.ofReal (W x / deriv W a) := by
      congr 1
      field_simp [ne_of_gt hWa, ne_of_gt hda]
