-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:37:09.26028+00:00
-- url     : https://prove2.me/submissions/9b45dfd5-aca6-436f-964f-e51eb1ac2758

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact total finite-partition variation of the canonical downward source
residual path, for any original BV sample and any ordered time partition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum
          (fun i => |R (u (i + 1)) - R (u i)|) =
        R (u n) - R (u 0) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV]
    with ω hmono
  let R (t : ℝ≥0) : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0).toReal
  refine ⟨R, ?_, hmono, ?_⟩
  · intro t
    rfl
  intro u hu n
  have hinc (i : ℕ) :
      0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hmono (hu (Nat.le_succ _)))
  calc
    (Finset.range n).sum
      (fun i => |R (u (i + 1)) - R (u i)|) =
      (Finset.range n).sum
        (fun i => R (u (i + 1)) - R (u i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact abs_of_nonneg (hinc i)
    _ = R (u n) - R (u 0) := by
          exact Finset.sum_range_sub (fun i => R (u i)) n
