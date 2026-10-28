-- Prove2me | solution 2 for AvramDividend.Classical.cstar_optimal_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:06:40.397018+00:00
-- url     : https://prove2.me/submissions/f0b5aeca-8034-483e-8e37-57ec0a8c00f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_cstar_scale_derivative_shape
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_shape

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  -- Principal route: decomp alternative 2 for 00fcfc56.
  -- Open cstar_lt_top supplies finiteness; IsScaleFunction's second
  -- conjunct supplies nonnegativity on [0,∞); Open shape package supplies
  -- the denominator/secant control; Proved of_shape closes the goal.
  -- Sketch at best until both Open premises are Proved.
  have hfinite : cstar W < ⊤ :=
    AvramDividend.Classical.cstar_lt_top X hX q hq W hW
  have hWnn : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := hW.2.1
  have hshape :=
    AvramDividend.Classical.cstar_scale_derivative_shape X hX q hq W hW hfinite
  exact AvramDividend.Classical.cstar_optimal_barrier_of_shape W hfinite hWnn hshape
