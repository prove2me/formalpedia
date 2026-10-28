-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_weighted_laplace_uniform_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:43:20.095782+00:00
-- url     : https://prove2.me/submissions/eb607f5d-42e0-4936-8f79-adf33026c720

import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Uniform weighted-Laplace control for q-scale functions with bounded
nonnegative discount parameters in the unbounded-variation case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ β : ℝ, 1 ≤ β ∧
        ∀ θ : ℝ, β ≤ θ →
          ∀ q : ℝ, 0 ≤ q → q ≤ Q →
            ∀ W : ℝ → ℝ, IsScaleFunction X q W →
              θ * (∫ x in Ioi (0 : ℝ),
                Real.exp (-(θ * x)) * W x) < ε := by
  intro ε hε
  obtain ⟨β, hβ, hlinear⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv Q hQ ε⁻¹
  refine ⟨β, hβ, ?_⟩
  intro θ hθ q hq hqQ W hW
  have hθnonneg : 0 ≤ θ := by linarith
  have hInv : 0 ≤ ε⁻¹ := inv_nonneg.mpr (le_of_lt hε)
  have hψ : q < X.ψ θ := by
    have hb := hlinear θ hθ
    have hmul : 0 ≤ ε⁻¹ * θ := mul_nonneg hInv hθnonneg
    linarith
  have hLap := (hW.2.2.2.2 θ hθnonneg hψ).2
  have hb : ε⁻¹ * θ < X.ψ θ - q := by
    have := hlinear θ hθ
    linarith
  calc
    θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x)
        = θ / (X.ψ θ - q) := by rw [hLap, div_eq_mul_inv]
    _ < ε := by
      apply (div_lt_iff₀ (sub_pos.mpr hψ)).2
      calc
        θ = ε * (ε⁻¹ * θ) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
        _ < ε * (X.ψ θ - q) :=
          mul_lt_mul_of_pos_left hb hε
