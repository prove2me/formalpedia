-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:50:40.788069+00:00
-- url     : https://prove2.me/submissions/85d76662-f3bb-4ec7-aca0-2bea4be76bb7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A pathwise uniform bound on arbitrary weighted source-remainder sums,
deduced from the monotonicity of the residual of the original BV source. -/
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
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (u n) - R (u 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV]
    with ω hmono
  let R (t : ℝ≥0) : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal
  refine ⟨R, ?_, hmono, ?_⟩
  · intro t
    rfl
  intro u hu n a M hM ha
  have hincr (i : ℕ) : 0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hmono (hu (Nat.le_succ i)))
  calc
    |(Finset.range n).sum (fun i =>
        a i * (R (u (i + 1)) - R (u i)))| ≤
        (Finset.range n).sum (fun i =>
          |a i * (R (u (i + 1)) - R (u i))|) := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ = (Finset.range n).sum (fun i =>
          |a i| * (R (u (i + 1)) - R (u i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, abs_of_nonneg (hincr i)]
    _ ≤ (Finset.range n).sum (fun i =>
          M * (R (u (i + 1)) - R (u i))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right (ha i) (hincr i)
    _ = M * ((Finset.range n).sum (fun i =>
          R (u (i + 1)) - R (u i))) := by
            rw [Finset.mul_sum]
    _ = M * (R (u n) - R (u 0)) := by
            exact congrArg (fun z : ℝ => M * z)
              (Finset.sum_range_sub (fun i => R (u i)) n)
