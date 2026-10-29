-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:45:37.676819+00:00
-- url     : https://prove2.me/submissions/c09c24c6-d8cc-4219-b925-797445fd7c2f

import Mathlib.Topology.Order.MonotoneConvergence
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
  have hpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    rw [hV x hx]
    exact mul_pos (Real.exp_pos _) 
      (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv x hx)
  obtain ⟨hmono, ⟨C, hC⟩⟩ :=
    unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot V hV
  exact positive_monotoneOn_bounded_tendsto_positive V hpos hmono ⟨C, hC⟩
