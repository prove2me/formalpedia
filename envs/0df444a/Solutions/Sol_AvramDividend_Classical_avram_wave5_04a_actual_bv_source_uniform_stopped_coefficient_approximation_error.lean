-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:15:41.791195+00:00
-- url     : https://prove2.me/submissions/0c906a0d-ae0c-4dfa-a465-5149bbd7e6dd

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A source-only, horizon-uniform C1 coefficient-approximation error
estimate for the genuine original BV source residual. No stochastic
integration identity is assumed, and R is the actual source residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a b : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (hab : ∀ i : ℕ, |a i - b i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
          (Finset.range n).sum (fun i =>
            b i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (τ ω) - R (u 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hstab⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop a b M hM hab
  calc
    |(Finset.range n).sum (fun i =>
        a i * (R (u (i + 1)) - R (u i))) -
      (Finset.range n).sum (fun i =>
        b i * (R (u (i + 1)) - R (u i)))| ≤
        M * (R (u n) - R (u 0)) :=
          hstab u hu n a b M hM hab
    _ ≤ M * (R (τ ω) - R (u 0)) := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_sub_right (hRmono hstop) (R (u 0))) hM
