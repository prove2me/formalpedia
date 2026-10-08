-- Prove2me | solution 1 for AvramDividend.Classical.cstar_optimal_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:56:57.748911+00:00
-- url     : https://prove2.me/submissions/6e8a1e0c-7b71-4b81-adce-2ea2bd2631f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_shape
import Theorems.Thm_AvramDividend_Classical_cstar_scale_derivative_shape

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Proposition 3(i), reduced to scale-function derivative shape.
The comparison itself uses the proved deterministic algebraic theorem. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  have hfinite : cstar W < ⊤ :=
    cstar_lt_top X hX q hq W hW
  have hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := hW.2.1
  have hshape :=
    cstar_scale_derivative_shape X hX q hq W hW hfinite
  exact cstar_optimal_barrier_of_shape W hfinite hnonneg hshape
