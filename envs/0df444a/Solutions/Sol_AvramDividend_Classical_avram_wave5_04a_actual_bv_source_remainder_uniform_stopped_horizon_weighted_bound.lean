-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:12:26.915056+00:00
-- url     : https://prove2.me/submissions/73bd52b8-eee0-46f7-9478-dd8728fba7af

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

/-- A partition-uniform real bound on every weighted original BV source
residual sum stopped below an arbitrary samplewise horizon. This gives
a pathwise finite-variation envelope independent of partition mesh. -/
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
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (τ ω) - R (u 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hbound⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop a M hM ha
  calc
    |(Finset.range n).sum (fun i =>
        a i * (R (u (i + 1)) - R (u i)))| ≤
        M * (R (u n) - R (u 0)) :=
          hbound u hu n a M hM ha
    _ ≤ M * (R (τ ω) - R (u 0)) := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_sub_right (hRmono hstop) (R (u 0))) hM
