-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_weighted_laplace_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:30:33.147977+00:00
-- url     : https://prove2.me/submissions/c032b818-799a-41d2-b922-fa38059c8ca1

import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_reciprocal_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The canonical scale-function Laplace transform has vanishing θ-scaled mass
at large Laplace parameters in the unbounded-variation case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    Tendsto
      (fun θ : ℝ => θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x))
      atTop (nhds 0) := by
  obtain ⟨β, hβ, hlinear⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv q hq 0
  have heq :
      (fun θ : ℝ => θ / (X.ψ θ - q)) =ᶠ[atTop]
        (fun θ : ℝ => θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x)) := by
    refine (eventually_ge_atTop β).mono ?_
    intro θ hθ
    have hθnonneg : 0 ≤ θ := by linarith
    have hψ : q < X.ψ θ := by
      simpa using hlinear θ hθ
    have hLap := (hW.2.2.2.2 θ hθnonneg hψ).2
    calc
      θ / (X.ψ θ - q) = θ * (X.ψ θ - q)⁻¹ := by rw [div_eq_mul_inv]
      _ = θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) := by rw [← hLap]
  exact (unbounded_psi_discount_reciprocal_tendsto_zero X hnbv q hq).congr' heq
