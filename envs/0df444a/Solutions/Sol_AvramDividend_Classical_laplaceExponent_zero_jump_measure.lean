-- Prove2me | solution 1 for AvramDividend.Classical.laplaceExponent_zero_jump_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:13:17.918579+00:00
-- url     : https://prove2.me/submissions/284a47bb-fb82-410e-9323-08d7b50c8c41

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical

theorem solution (c σ θ : ℝ) :
    laplaceExponent c σ (0 : Measure ℝ) θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 := by
  simp [laplaceExponent]
