-- Prove2me | solution 4 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:25:39.639329+00:00
-- url     : https://prove2.me/submissions/a33a1b0a-ded9-4110-b996-c3c20127285a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_monotoneOn_bounded_tendsto_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strictly positive, nondecreasing, uniformly bounded Esscher scale
function converges to a strictly positive finite limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  obtain ⟨hmono, hupper⟩ :=
    unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot V hV
  apply positive_monotoneOn_bounded_tendsto_positive V ?_ hmono hupper
  intro x hx
  rw [hV x hx]
  exact mul_pos (Real.exp_pos _) 
    (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv x hx)
