-- Prove2me | solution 2 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T09:29:38.98999+00:00
-- url     : https://prove2.me/submissions/a75b8d17-4009-4fee-8b5e-3d19fc3f7ce3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_boundary_value
import Theorems.Thm_AvramDividend_Classical_barrier_value_scale_factor

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Proposition 1 (eq. 3.12): the barrier strategy value is the scale-function
-- ratio. The proof factors through two analytic inputs, each an openly
-- published sibling theorem used here as a sketch hypothesis:
-- (A) the boundary identity at the barrier (eq. 3.13, clean preamble), and
-- (B) the strong-Markov scale factor carrying the x-dependence.
-- Everything else -- nonnegativity of W, the ENNReal product rule and the
-- real field cancellation -- is proved inline in Lean.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by
  have hA : dividendValue X q a (barrierStrategy X a a)
      = ENNReal.ofReal (W a / deriv W a) :=
    barrier_boundary_value X hX q hq W hW a ha
  obtain ⟨hWa, hFac⟩ :=
    barrier_value_scale_factor X hX q hq W hW a ha x hx0 hxa
  have hWx : 0 ≤ W x := by
    unfold IsScaleFunction at hW
    exact hW.2.1 x hx0
  have hWane : W a ≠ 0 := ne_of_gt hWa
  have hNonneg : 0 ≤ W x / W a := div_nonneg hWx (le_of_lt hWa)
  rw [hFac, hA, ← ENNReal.ofReal_mul hNonneg]
  congr 1
  by_cases hD : deriv W a = 0
  · simp [hD]
  · field_simp
