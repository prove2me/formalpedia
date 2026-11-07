-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_intrinsic_integer_horizon_transform_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:02:50.616998+00:00
-- url     : https://prove2.me/submissions/283c773d-bdea-4d3b-99ff-115a929f009f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_intrinsic_one_step_transform_factor
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_zero_horizon_intrinsic_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Integer-horizon source Laplace powers follow from adjacent-window factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) ^ n := by
  intro n k
  induction n with
  | zero =>
      simpa only [pow_zero, Nat.cast_zero] using
        (avram_bv_jump8_zero_horizon_intrinsic_moment X hX hBV k)
  | succ n ih =>
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ, ih] using
        (avram_bv_jump8_intrinsic_one_step_transform_factor X hX hBV n k)
