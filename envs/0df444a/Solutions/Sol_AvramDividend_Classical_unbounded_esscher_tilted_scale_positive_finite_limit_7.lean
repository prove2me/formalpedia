-- Prove2me | solution 7 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:48:17.011935+00:00
-- url     : https://prove2.me/submissions/a384a0e2-e3bf-4596-b8fb-4c2c9cc9fb5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound
import Theorems.Thm_AvramDividend_Classical_positive_monotoneOn_bounded_tendsto_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  have hWpos : ∀ a : ℝ, 0 < a → 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv
  have hpos : ∀ x : ℝ, 0 < x → 0 < V x := fun x hx => by
    rw [hV x hx]
    exact mul_pos (Real.exp_pos _) (hWpos x hx)
  have hMB :=
    AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot V hV
  exact AvramDividend.Classical.positive_monotoneOn_bounded_tendsto_positive
    V hpos hMB.1 hMB.2
