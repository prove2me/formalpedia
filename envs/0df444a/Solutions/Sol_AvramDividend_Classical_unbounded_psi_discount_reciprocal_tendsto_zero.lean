-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_psi_discount_reciprocal_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:17:06.456289+00:00
-- url     : https://prove2.me/submissions/8f24f1e3-7350-4894-bfed-11a95d05fae2

import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_reciprocal_small
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The discounted Lévy Laplace reciprocal converges to zero in the atTop filter
for every spectrally negative Lévy process of unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun θ : ℝ => θ / (X.ψ θ - q)) atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    obtain ⟨β, _, hβ⟩ :=
      unbounded_psi_discount_reciprocal_small X hnbv q hq 1 (by norm_num)
    refine (eventually_ge_atTop β).mono ?_
    intro θ hθ
    have hnonneg := (hβ θ hθ).1
    linarith
  · intro b hb
    obtain ⟨β, _, hβ⟩ :=
      unbounded_psi_discount_reciprocal_small X hnbv q hq b hb
    refine (eventually_ge_atTop β).mono ?_
    intro θ hθ
    exact (hβ θ hθ).2
