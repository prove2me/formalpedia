-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_BV_intrinsic_source_residual_exact_finite_partition_total_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:30:37.631398+00:00
-- url     : https://prove2.me/submissions/3124eaba-f25d-4089-9cfb-ef7e65ef6fd4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every finite monotone physical-time grid records exactly the
variation of the original-source downward residual, including any
continuous variation omitted by the intrinsic negative left jumps. -/
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
      (∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s)) ∧
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (hu : Monotone u),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) =
          R (u n) - R (u 0) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hω
  refine ⟨R, hRdef, hRmono, hinterval, ?_⟩
  intro n u hu
  calc
    (Finset.range n).sum (fun i =>
      |R (u (i + 1)) - R (u i)|) =
        (Finset.range n).sum (fun i =>
          R (u (i + 1)) - R (u i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact abs_of_nonneg
              (sub_nonneg.mpr (hRmono (hu (Nat.le_succ i))))
    _ = R (u n) - R (u 0) :=
      Finset.sum_range_sub (fun i => R (u i)) n
