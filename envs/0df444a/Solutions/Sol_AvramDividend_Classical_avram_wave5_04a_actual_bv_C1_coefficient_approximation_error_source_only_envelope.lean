-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_C1_coefficient_approximation_error_source_only_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:45:43.750583+00:00
-- url     : https://prove2.me/submissions/847ff2b1-5e70-409f-bc16-048ba1944bd9

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Uniform approximation of coefficients in a source C1 finite-variation
sum has a path-only bound: the residual is absent from the RHS. -/
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
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
        (a b : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
        (hclose : ∀ i : ℕ, |a i - b i| ≤ ε),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
          (Finset.range n).sum (fun i =>
          b i * (R (u (i + 1)) - R (u i)))| ≤
          ε * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hbound⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro u hu n a b ε hε hclose
  have hsum :
      (Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
      (Finset.range n).sum (fun i =>
          b i * (R (u (i + 1)) - R (u i))) =
      (Finset.range n).sum (fun i =>
        (a i - b i) * (R (u (i + 1)) - R (u i))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  rw [hsum]
  exact hbound u hu n (fun i => a i - b i) ε hε hclose
