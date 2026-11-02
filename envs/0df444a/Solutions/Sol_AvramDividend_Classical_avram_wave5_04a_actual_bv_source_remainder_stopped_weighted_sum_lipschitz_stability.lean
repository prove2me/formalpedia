-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:05:58.573488+00:00
-- url     : https://prove2.me/submissions/5906335a-c860-4c40-8681-97ae892e2646

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV source-residual finite-variation contribution
is Lipschitz in the sup norm of its sampled coefficient sequence. This is
the quantitative C1-approximation stability needed before Ito-Meyer. -/
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
        (a b : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (hab : ∀ i : ℕ, |a i - b i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
          (Finset.range n).sum (fun i =>
            b i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (u n) - R (u 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hbound⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro u hu n a b M hM hab
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
  exact hbound u hu n (fun i => a i - b i) M hM hab
