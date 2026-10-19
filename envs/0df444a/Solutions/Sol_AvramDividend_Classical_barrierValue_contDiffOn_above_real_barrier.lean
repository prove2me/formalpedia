-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_contDiffOn_above_real_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:11:55.685263+00:00
-- url     : https://prove2.me/submissions/a894f5df-a25c-408b-a0bc-47d16af03a2a

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    ContDiffOn ℝ 2 (barrierValue W a) (Ioi a) := by
  have hright : ∀ x ∈ Ioi a,
      barrierValue W a x =
        x - a + divE (W a) (scaleDeriv W a) := by
    intro x hx
    have hx0 : ¬ x < 0 := not_lt.mpr (ha.trans hx.le)
    have hxa : ¬ x ≤ a := not_le.mpr hx
    simp only [barrierValue, if_neg hx0, if_neg hxa]
  have hsmooth :
      ContDiffOn ℝ 2
        (fun x : ℝ => x - a + divE (W a) (scaleDeriv W a))
        (Ioi a) := by
    exact (contDiffOn_id.sub contDiffOn_const).add contDiffOn_const
  exact hsmooth.congr hright
