-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_smooth_below_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:58:22.885205+00:00
-- url     : https://prove2.me/submissions/e8c093dc-ded5-4803-9c2e-55d0e3229cf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) := by
  let c : ℝ := (cstar W).toReal
  let S : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hcne : cstar W ≠ 0 := ne_of_gt hcpos
  have hcR : 0 < c := ENNReal.toReal_pos hcne hctop
  have hdc : 0 < deriv W c :=
    scaleDeriv_pos X hX q hq W hW c hcR
  have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
    simp [scaleDeriv, c, hcR.ne']
  have hdiv (y : ℝ) : divE (W y) (scaleDeriv W c) = W y / deriv W c := by
    simp [hscale, divE]
  have hS : S ⊆ Ioi (0 : ℝ) := by
    intro y hy
    change 0 < y ∧ ENNReal.ofReal y < cstar W at hy
    exact hy.1
  have heq : ∀ y ∈ S, vcstar W y = W y / deriv W c := by
    intro y hy
    change 0 < y ∧ ENNReal.ofReal y < cstar W at hy
    have hycR : y < c :=
      (ENNReal.ofReal_lt_iff_lt_toReal hy.1.le hctop).mp hy.2
    simp [vcstar, barrierValue, c, not_lt.mpr hy.1.le, hycR.le, hdiv]

  constructor
  · intro hnbv
    rcases h_smooth with hσ | hrest
    · have hW2 :=
        scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
      exact ((hW2.mono hS).div_const (deriv W c)).congr heq
    · rcases hrest with hbv | hvc2
      · exact (hnbv hbv).elim
      · exact hvc2.mono hS
  · intro hbv
    have hW1 := scaleFunction_contDiff_one X hX q hq W hW
    exact ((hW1.mono hS).div_const (deriv W c)).congr heq
