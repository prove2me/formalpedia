-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_lipschitzOn_positive_compact_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:19:19.035162+00:00
-- url     : https://prove2.me/submissions/0e98f161-e67f-4fcf-b38e-038a96720860

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A bounded-variation q-scale function is uniformly Lipschitz on each
compact strip staying strictly above the discontinuous zero boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (ε a : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ≥0, LipschitzOnWith K W (Icc ε a) := by
  have hC1 :
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hBV
  have hsub : Icc ε a ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le hε hy.1
  have hstrip : ContDiffOn ℝ 1 W (Icc ε a) :=
    hC1.mono hsub
  exact hstrip.exists_lipschitzOnWith (by norm_num)
    (convex_Icc ε a) isCompact_Icc
