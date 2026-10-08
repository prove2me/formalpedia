-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_eventually_ge_exp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T18:53:21.903852+00:00
-- url     : https://prove2.me/submissions/115b201f-e237-4e19-a39c-b6a39af8f4b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one X hX q hq W hW
  obtain ⟨hpositive, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    have hwithin : DifferentiableWithinAt ℝ W (Ioi 0) x :=
      hreg.differentiableOn_one x hx
    exact hwithin.differentiableAt (isOpen_Ioi.mem_nhds hx)
  have hd : ∀ x : ℝ, 0 < x → φ * W x ≤ deriv W x := by
    intro x hx
    exact normalized_derivative_lower_bound φ x htilt hx (hdiff x hx)
  have hOne : (0 : ℝ) < 1 := by norm_num
  obtain ⟨c, hc, hbound⟩ :=
    normalized_eventual_derivative_growth φ 1 hφ hOne
      (hpositive 1 hOne) htilt hd
  exact ⟨φ, c, hφ, hc, hbound⟩
