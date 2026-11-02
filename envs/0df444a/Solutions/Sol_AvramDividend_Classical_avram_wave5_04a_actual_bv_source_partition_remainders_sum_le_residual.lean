-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_partition_remainders_sum_le_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:21:26.386396+00:00
-- url     : https://prove2.me/submissions/583e5970-227a-49b6-96ea-e1376f0ed79a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Along every actual BV source partition, the complete source left-jump
magnitudes admit real nonnegative cell remainders whose finite sums are
uniformly bounded by the genuine original drift-residual increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (hu : Monotone u),
      ∃ r : ℕ → ℝ,
        (∀ i : ℕ, 0 ≤ r i ∧
          (∑' (v : ℝ≥0),
            if u i < v ∧ v ≤ u (i + 1) then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal + r i =
          ((u (i + 1) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
            ((u i : ℝ) * X.drift - X.X (u i) ω)) ∧
        (∀ n : ℕ,
          (∑ i ∈ Finset.range n, r i) ≤
            ((u n : ℝ) * X.drift - X.X (u n) ω) -
              ((u 0 : ℝ) * X.drift - X.X (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder X hBV]
    with ω hω
  intro u hu
  classical
  have hstep (i : ℕ) : ∃ r : ℝ, 0 ≤ r ∧
      (∑' (v : ℝ≥0),
        if u i < v ∧ v ≤ u (i + 1) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal + r =
      ((u (i + 1) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
        ((u i : ℝ) * X.drift - X.X (u i) ω) := by
    exact hω (u i) (u (i + 1)) (hu (Nat.le_succ _))
  choose r hr_nonneg hr_balance using hstep
  refine ⟨r, ?_, ?_⟩
  · intro i
    exact ⟨hr_nonneg i, hr_balance i⟩
  · intro n
    have hle (i : ℕ) : r i ≤
        ((u (i + 1) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
          ((u i : ℝ) * X.drift - X.X (u i) ω) := by
      have hm : 0 ≤
          (∑' (v : ℝ≥0),
            if u i < v ∧ v ≤ u (i + 1) then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal := ENNReal.toReal_nonneg
      linarith only [hr_balance i, hm]
    change (Finset.range n).sum r ≤
      ((u n : ℝ) * X.drift - X.X (u n) ω) -
        ((u 0 : ℝ) * X.drift - X.X (u 0) ω)
    calc
      (Finset.range n).sum r ≤
          (Finset.range n).sum (fun i =>
            ((u (i + 1) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
              ((u i : ℝ) * X.drift - X.X (u i) ω)) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hle i
      _ = ((u n : ℝ) * X.drift - X.X (u n) ω) -
            ((u 0 : ℝ) * X.drift - X.X (u 0) ω) := by
              exact Finset.sum_range_sub
                (fun i => (u i : ℝ) * X.drift - X.X (u i) ω) n
