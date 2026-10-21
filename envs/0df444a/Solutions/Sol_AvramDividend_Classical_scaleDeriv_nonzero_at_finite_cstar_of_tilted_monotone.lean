-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T05:18:20.692983+00:00
-- url     : https://prove2.me/submissions/73f3b36f-3ec1-433c-8806-8c6ac13e204a

import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The barrier normaliser is non-zero at a finite positive optimal barrier.

This is the hypothesis `hk` of the aggregator
`scaleFunction_generator_q_harmonic_of_nonzero_factor` and of each of its
three branch theorems.  It says that the scaled barrier value
`x ↦ W x / deriv W c*` is well defined below `c*`, which is what makes the
transfer from scale-function q-harmonicity to the exact dividend value
meaningful.

The proof has two parts.  The Proved
`scaleDeriv_pos_of_tilted_positive_monotone` gives `0 < deriv W x` for every
`x > 0`, and at the positive barrier level this is `0 < deriv W c*`.  Then
`scaleDeriv W c*` is the cast of the real number `deriv W c*` into `EReal`
(the barrier level is non-zero), and `divE 1 d` for a finite `d` is
`1 / d.toReal`, which is non-zero because `deriv W c*` is a positive real.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : (cstar W).toReal > 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  -- The scale-function derivative is strictly positive on the positive axis.
  have hder : 0 < deriv W (cstar W).toReal :=
    scaleDeriv_pos_of_tilted_positive_monotone X hX q hq W hW hpos hdiff htilt
      (cstar W).toReal hc
  -- The barrier level is positive, hence non-zero, so the scale derivative
  -- there is the cast of a real number rather than the right-hand slope.
  have hne : (cstar W).toReal ≠ 0 := ne_of_gt hc
  rw [scaleDeriv, if_neg hne]
  -- The cast of a real number is not `⊤`, and its `toReal` is that number.
  have hne' : ((deriv W (cstar W).toReal : ℝ) : EReal) ≠ ⊤ :=
    EReal.coe_ne_top _
  rw [divE, if_neg hne']
  rw [EReal.toReal_coe]
  exact div_ne_zero (by norm_num) (ne_of_gt hder)
